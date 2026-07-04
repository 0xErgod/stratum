//! # stratum-kernel
//!
//! A Jupyter kernel for the Stratum DSL. It speaks the Jupyter messaging
//! protocol (v5.3) over **pure-Rust ZeroMQ** (the `zeromq` crate) — no system
//! `libzmq`, which matters on Windows — and delegates all cell-level work to the
//! substrate-agnostic [`stratum_notebook`] core.
//!
//! The wire protocol (HMAC signing, multipart framing, the five sockets, the
//! handshake) is proven end to end by the acceptance test. `execute_request`
//! cells are evaluated by [`stratum_notebook::evaluate`] against a persistent
//! session [`Namespace`]; the resulting MIME bundles / errors are translated
//! into iopub `display_data` / `error` messages. The `evaluate` call is
//! `catch_unwind`-guarded so an ordinary panic in the core surfaces as an error
//! reply rather than tearing down the session.
//!
//! ## Sockets
//!
//! | Role      | ZMQ type | Purpose                                   |
//! |-----------|----------|-------------------------------------------|
//! | shell     | ROUTER   | execute / kernel_info requests            |
//! | control   | ROUTER   | shutdown / interrupt (priority channel)   |
//! | iopub     | PUB      | status, stream, execute_result broadcasts |
//! | stdin     | ROUTER   | input_request (unused in Phase 0)         |
//! | heartbeat | REP      | echo bytes so the frontend sees liveness  |

#![forbid(unsafe_code)]

mod wire;

use std::sync::Arc;

use anyhow::Context as _;
use bytes::Bytes;
use serde_json::{json, Value};
use tokio::sync::{mpsc, Mutex};
use zeromq::{PubSocket, RepSocket, RouterSocket, Socket, SocketRecv, SocketSend, ZmqMessage};

use stratum_notebook::{CellError, CellOutcome, IsComplete, MimeBundle, Namespace};
use wire::{ConnectionInfo, Header, Message, Outgoing, PROTOCOL_VERSION};

/// Shared handle to the single PUB socket used for all iopub broadcasts.
type IoPub = Arc<Mutex<PubSocket>>;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let conn_path = std::env::args()
        .nth(1)
        .context("usage: stratum-kernel <connection_file>")?;
    let raw = std::fs::read_to_string(&conn_path)
        .with_context(|| format!("reading connection file {conn_path}"))?;
    let conn: ConnectionInfo =
        serde_json::from_str(&raw).context("parsing connection file as JSON")?;
    anyhow::ensure!(
        conn.scheme_supported(),
        "unsupported signature_scheme {:?}; only hmac-sha256 is implemented",
        conn.signature_scheme
    );
    let key: Vec<u8> = conn.key_bytes().to_vec();
    let kernel_session = uuid::Uuid::new_v4().to_string();

    // Bind the five sockets described in the connection file.
    let mut shell = RouterSocket::new();
    shell.bind(&conn.endpoint(conn.shell_port)).await?;
    let mut control = RouterSocket::new();
    control.bind(&conn.endpoint(conn.control_port)).await?;
    let mut stdin = RouterSocket::new();
    stdin.bind(&conn.endpoint(conn.stdin_port)).await?;
    let mut heartbeat = RepSocket::new();
    heartbeat.bind(&conn.endpoint(conn.hb_port)).await?;
    let mut iopub_sock = PubSocket::new();
    iopub_sock.bind(&conn.endpoint(conn.iopub_port)).await?;
    let iopub: IoPub = Arc::new(Mutex::new(iopub_sock));

    // Announce startup on iopub (no parent — this is unsolicited).
    publish(
        &iopub,
        &key,
        "status",
        &kernel_session,
        json!({}),
        json!({ "execution_state": "starting" }),
    )
    .await?;
    publish(
        &iopub,
        &key,
        "status",
        &kernel_session,
        json!({}),
        json!({ "execution_state": "idle" }),
    )
    .await?;

    // Heartbeat: echo every frame straight back.
    tokio::spawn(async move {
        while let Ok(msg) = heartbeat.recv().await {
            if heartbeat.send(msg).await.is_err() {
                break;
            }
        }
    });

    // stdin: Phase 0 has no input_request flow; drain so the socket stays healthy.
    tokio::spawn(async move { while stdin.recv().await.is_ok() {} });

    let (shutdown_tx, mut shutdown_rx) = mpsc::channel::<()>(1);

    // Control channel (shutdown / interrupt).
    {
        let iopub = iopub.clone();
        let key = key.clone();
        let session = kernel_session.clone();
        let tx = shutdown_tx.clone();
        tokio::spawn(async move {
            let _ = control_loop(control, iopub, key, session, tx).await;
        });
    }

    // Shell channel (kernel_info / execute).
    {
        let iopub = iopub.clone();
        let key = key.clone();
        let session = kernel_session.clone();
        tokio::spawn(async move {
            let _ = shell_loop(shell, iopub, key, session).await;
        });
    }

    // Block until a shutdown_request arrives, then give the reply a moment to
    // flush before the process exits.
    let _ = shutdown_rx.recv().await;
    tokio::time::sleep(std::time::Duration::from_millis(100)).await;
    Ok(())
}

/// The shell request loop: receive, verify+decode, handle, reply.
async fn shell_loop(
    mut shell: RouterSocket,
    iopub: IoPub,
    key: Vec<u8>,
    kernel_session: String,
) -> anyhow::Result<()> {
    let mut execution_count: i64 = 0;
    // The session namespace: DSL definitions and directive results accumulate
    // here across execute_requests, owned by the (single) shell loop.
    let mut namespace = Namespace::new();
    loop {
        let zmsg = shell.recv().await?;
        let msg = match Message::parse(to_frames(zmsg), &key) {
            Ok(m) => m,
            Err(err) => {
                // A bad signature (or malformed frame) is dropped, never
                // processed — no reply, no side effects.
                eprintln!("shell: rejected message: {err}");
                continue;
            }
        };
        if let Some(reply) = handle_shell(
            &msg,
            &iopub,
            &key,
            &kernel_session,
            &mut execution_count,
            &mut namespace,
        )
        .await?
        {
            shell.send(from_frames(reply)).await?;
        }
    }
}

/// Handle one shell request, returning the reply frames to send (if any).
async fn handle_shell(
    msg: &Message,
    iopub: &IoPub,
    key: &[u8],
    kernel_session: &str,
    execution_count: &mut i64,
    namespace: &mut Namespace,
) -> anyhow::Result<Option<Vec<Vec<u8>>>> {
    let session = session_of(msg, kernel_session);
    match msg.msg_type() {
        "kernel_info_request" => {
            // Bracket with iopub busy/idle like every other shell handler.
            // `jupyter_client.wait_for_ready` (used on startup by JupyterLab and
            // the VS Code Jupyter extension) sends a `kernel_info_request` and
            // blocks until it sees a `status: idle` on iopub parented to it; a
            // kernel that replies on shell but never publishes that idle hangs
            // the frontend's readiness check.
            publish_status(iopub, key, &session, msg, "busy").await?;
            let frames = reply_to(msg, "kernel_info_reply", &session, kernel_info_content())
                .into_frames(key);
            publish_status(iopub, key, &session, msg, "idle").await?;
            Ok(Some(frames))
        }
        "execute_request" => {
            let code = msg
                .content
                .get("code")
                .and_then(Value::as_str)
                .unwrap_or("")
                .to_string();
            let silent = msg
                .content
                .get("silent")
                .and_then(Value::as_bool)
                .unwrap_or(false);

            // busy
            publish(
                iopub,
                key,
                "status",
                &session,
                msg.header.clone(),
                json!({ "execution_state": "busy" }),
            )
            .await?;

            *execution_count += 1;
            let count = *execution_count;

            // echo the input back to the frontend
            publish(
                iopub,
                key,
                "execute_input",
                &session,
                msg.header.clone(),
                json!({ "code": code, "execution_count": count }),
            )
            .await?;

            // Delegate all cell-level work to the substrate-agnostic notebook
            // core, which mutates the persistent session namespace.
            //
            // Defense-in-depth: contain an *ordinary* panic in the notebook core
            // so one bad cell surfaces as an error reply rather than tearing down
            // the shell loop / session. (A stack overflow is uncatchable — the
            // depth guards inside `stratum-notebook` are what prevent that.)
            let outcome: CellOutcome =
                match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    stratum_notebook::evaluate(&code, namespace)
                })) {
                    Ok(outcome) => outcome,
                    Err(payload) => {
                        let detail = panic_detail(&*payload);
                        CellOutcome::err(CellError::new(
                            "InternalError",
                            format!("internal error while evaluating the cell: {detail}"),
                        ))
                    }
                };

            if !silent {
                // Streamed stdout, if any.
                if !outcome.stream_stdout.is_empty() {
                    publish(
                        iopub,
                        key,
                        "stream",
                        &session,
                        msg.header.clone(),
                        json!({ "name": "stdout", "text": outcome.stream_stdout }),
                    )
                    .await?;
                }
                // Each rich display becomes one iopub display_data.
                for bundle in &outcome.displays {
                    publish(
                        iopub,
                        key,
                        "display_data",
                        &session,
                        msg.header.clone(),
                        json!({
                            "data": mime_data(bundle),
                            "metadata": {},
                            "transient": {},
                        }),
                    )
                    .await?;
                }
                // An error becomes an iopub `error` broadcast.
                if let Some(err) = &outcome.error {
                    publish(
                        iopub,
                        key,
                        "error",
                        &session,
                        msg.header.clone(),
                        json!({
                            "ename": err.ename,
                            "evalue": err.evalue,
                            "traceback": err.traceback,
                        }),
                    )
                    .await?;
                }
            }

            let reply_content = if let Some(err) = &outcome.error {
                json!({
                    "status": "error",
                    "execution_count": count,
                    "ename": err.ename,
                    "evalue": err.evalue,
                    "traceback": err.traceback,
                })
            } else {
                json!({
                    "status": "ok",
                    "execution_count": count,
                    "user_expressions": {},
                    "payload": [],
                })
            };
            let reply = reply_to(msg, "execute_reply", &session, reply_content);
            let frames = reply.into_frames(key);

            // idle
            publish(
                iopub,
                key,
                "status",
                &session,
                msg.header.clone(),
                json!({ "execution_state": "idle" }),
            )
            .await?;

            Ok(Some(frames))
        }
        "complete_request" => {
            let code = str_field(msg, "code");
            let cursor_pos = usize_field(msg, "cursor_pos");
            publish_status(iopub, key, &session, msg, "busy").await?;

            // Panic-safe: the notebook service is panic-free by design, but we
            // contain any ordinary panic so an interactivity request can never
            // tear down the shell loop.
            let comp = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                stratum_notebook::complete(&code, cursor_pos, namespace)
            }))
            .unwrap_or_default();
            let content = json!({
                "status": "ok",
                "matches": comp.matches,
                "cursor_start": comp.cursor_start,
                "cursor_end": comp.cursor_end,
                "metadata": {},
            });
            let frames = reply_to(msg, "complete_reply", &session, content).into_frames(key);
            publish_status(iopub, key, &session, msg, "idle").await?;
            Ok(Some(frames))
        }
        "inspect_request" => {
            let code = str_field(msg, "code");
            let cursor_pos = usize_field(msg, "cursor_pos");
            publish_status(iopub, key, &session, msg, "busy").await?;

            let inspection = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                stratum_notebook::inspect(&code, cursor_pos, namespace)
            }))
            .unwrap_or(None);
            let (found, data) = match inspection {
                Some(i) => {
                    let mut d = serde_json::Map::new();
                    d.insert("text/plain".to_string(), Value::String(i.text_plain));
                    if let Some(html) = i.text_html {
                        d.insert("text/html".to_string(), Value::String(html));
                    }
                    (true, Value::Object(d))
                }
                None => (false, json!({})),
            };
            let content = json!({
                "status": "ok",
                "found": found,
                "data": data,
                "metadata": {},
            });
            let frames = reply_to(msg, "inspect_reply", &session, content).into_frames(key);
            publish_status(iopub, key, &session, msg, "idle").await?;
            Ok(Some(frames))
        }
        "is_complete_request" => {
            let code = str_field(msg, "code");
            publish_status(iopub, key, &session, msg, "busy").await?;

            let verdict = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                stratum_notebook::is_complete(&code)
            }));
            let (status, indent) = match verdict {
                Ok(IsComplete::Complete) => ("complete", String::new()),
                Ok(IsComplete::Incomplete { indent }) => ("incomplete", indent),
                Ok(IsComplete::Invalid) => ("invalid", String::new()),
                // A panic in the classifier: report "unknown" so the frontend
                // falls back to a heuristic rather than hanging.
                Err(_) => ("unknown", String::new()),
            };
            let content = json!({ "status": status, "indent": indent });
            let frames = reply_to(msg, "is_complete_reply", &session, content).into_frames(key);
            publish_status(iopub, key, &session, msg, "idle").await?;
            Ok(Some(frames))
        }
        // Unknown request types are ignored.
        _ => Ok(None),
    }
}

/// A string field of a request's content, or `""` when absent.
fn str_field(msg: &Message, field: &str) -> String {
    msg.content
        .get(field)
        .and_then(Value::as_str)
        .unwrap_or("")
        .to_string()
}

/// A `usize` field of a request's content, or `0` when absent / negative.
fn usize_field(msg: &Message, field: &str) -> usize {
    msg.content
        .get(field)
        .and_then(Value::as_u64)
        .and_then(|n| usize::try_from(n).ok())
        .unwrap_or(0)
}

/// Publish an iopub `status` broadcast parented to `req` (busy/idle bracketing).
async fn publish_status(
    iopub: &IoPub,
    key: &[u8],
    session: &str,
    req: &Message,
    state: &str,
) -> anyhow::Result<()> {
    publish(
        iopub,
        key,
        "status",
        session,
        req.header.clone(),
        json!({ "execution_state": state }),
    )
    .await
}

/// The control loop: shutdown and interrupt requests.
async fn control_loop(
    mut control: RouterSocket,
    _iopub: IoPub,
    key: Vec<u8>,
    kernel_session: String,
    shutdown: mpsc::Sender<()>,
) -> anyhow::Result<()> {
    loop {
        let zmsg = control.recv().await?;
        let msg = match Message::parse(to_frames(zmsg), &key) {
            Ok(m) => m,
            Err(err) => {
                eprintln!("control: rejected message: {err}");
                continue;
            }
        };
        let session = session_of(&msg, &kernel_session);
        match msg.msg_type() {
            "shutdown_request" => {
                let restart = msg
                    .content
                    .get("restart")
                    .and_then(Value::as_bool)
                    .unwrap_or(false);
                let reply = reply_to(
                    &msg,
                    "shutdown_reply",
                    &session,
                    json!({ "status": "ok", "restart": restart }),
                );
                control.send(from_frames(reply.into_frames(&key))).await?;
                let _ = shutdown.send(()).await;
                return Ok(());
            }
            "interrupt_request" => {
                let reply = reply_to(&msg, "interrupt_reply", &session, json!({ "status": "ok" }));
                control.send(from_frames(reply.into_frames(&key))).await?;
            }
            "kernel_info_request" => {
                let reply = reply_to(&msg, "kernel_info_reply", &session, kernel_info_content());
                control.send(from_frames(reply.into_frames(&key))).await?;
            }
            _ => {}
        }
    }
}

/// Build the `kernel_info_reply` content. `pygments_lexer` names the Stratum
/// Pygments lexer shipped under `editors/pygments/` (installed separately);
/// `.strat` cells are live-highlighted in JupyterLab 4 via the CodeMirror 6
/// language keyed off the `text/x-stratum` mimetype (`editors/jupyterlab-stratum/`).
fn kernel_info_content() -> Value {
    json!({
        "status": "ok",
        "protocol_version": PROTOCOL_VERSION,
        "implementation": "stratum",
        "implementation_version": env!("CARGO_PKG_VERSION"),
        "language_info": {
            "name": "stratum",
            "version": env!("CARGO_PKG_VERSION"),
            "mimetype": "text/x-stratum",
            "file_extension": ".strat",
            "pygments_lexer": "stratum",
            "codemirror_mode": "text/x-stratum",
        },
        "banner": "Stratum kernel — executable core for the πρσϕ-Formalism (reflective ρ-calculus). DSL cells define processes; %-directives explore, model-check, and compare them. Try %help.",
        "help_links": [],
    })
}

/// Extract a human-readable message from a caught panic payload.
fn panic_detail(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "unknown panic".to_string()
    }
}

/// Build the Jupyter `data` map for a [`MimeBundle`], including only the MIME
/// keys the renderer populated (`text/plain` is always present).
fn mime_data(bundle: &MimeBundle) -> Value {
    let mut data = serde_json::Map::new();
    data.insert(
        "text/plain".to_string(),
        Value::String(bundle.text_plain.clone()),
    );
    if let Some(html) = &bundle.text_html {
        data.insert("text/html".to_string(), Value::String(html.clone()));
    }
    if let Some(svg) = &bundle.image_svg {
        data.insert("image/svg+xml".to_string(), Value::String(svg.clone()));
    }
    Value::Object(data)
}

/// Compose a ROUTER reply that inherits the request's identities and header.
fn reply_to(req: &Message, msg_type: &str, session: &str, content: Value) -> Outgoing {
    Outgoing {
        identities: req.identities.clone(),
        header: Header::new(msg_type, session, "kernel"),
        parent_header: req.header.clone(),
        metadata: json!({}),
        content,
    }
}

/// Publish an iopub broadcast. `topic` is the ZMQ subscription prefix (frontends
/// subscribe to `""`, so any topic is delivered) and doubles as the `msg_type`.
async fn publish(
    iopub: &IoPub,
    key: &[u8],
    msg_type: &str,
    session: &str,
    parent: Value,
    content: Value,
) -> anyhow::Result<()> {
    let out = Outgoing {
        identities: vec![msg_type.as_bytes().to_vec()],
        header: Header::new(msg_type, session, "kernel"),
        parent_header: parent,
        metadata: json!({}),
        content,
    };
    let mut sock = iopub.lock().await;
    sock.send(from_frames(out.into_frames(key))).await?;
    Ok(())
}

/// The session id to stamp on outgoing messages: the caller's when present
/// (so a frontend associates replies), else the kernel's own.
fn session_of(msg: &Message, kernel_session: &str) -> String {
    msg.header
        .get("session")
        .and_then(Value::as_str)
        .filter(|s| !s.is_empty())
        .unwrap_or(kernel_session)
        .to_string()
}

/// Convert an inbound `ZmqMessage` into owned frame byte-vectors.
fn to_frames(msg: ZmqMessage) -> Vec<Vec<u8>> {
    msg.into_vec().into_iter().map(|b| b.to_vec()).collect()
}

/// Convert outbound frame byte-vectors into a `ZmqMessage`.
fn from_frames(frames: Vec<Vec<u8>>) -> ZmqMessage {
    let frames: Vec<Bytes> = frames.into_iter().map(Bytes::from).collect();
    ZmqMessage::try_from(frames).expect("outgoing message always has ≥1 frame")
}
