//! # stratum-kernel
//!
//! A Jupyter kernel for the Stratum DSL. It speaks the Jupyter messaging
//! protocol (v5.3) over **pure-Rust ZeroMQ** (the `zeromq` crate) — no system
//! `libzmq`, which matters on Windows — and delegates all cell-level work to the
//! substrate-agnostic [`stratum_notebook`] core.
//!
//! Phase 0 is a *walking skeleton*: it proves the wire protocol end to end
//! (HMAC signing, multipart framing, the five sockets, the handshake) by
//! answering `kernel_info_request` and echoing `execute_request` cells back as
//! output. Language-aware evaluation arrives in later phases inside
//! `stratum-notebook`.
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
        if let Some(reply) =
            handle_shell(&msg, &iopub, &key, &kernel_session, &mut execution_count).await?
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
) -> anyhow::Result<Option<Vec<Vec<u8>>>> {
    let session = session_of(msg, kernel_session);
    match msg.msg_type() {
        "kernel_info_request" => {
            let reply = reply_to(msg, "kernel_info_reply", &session, kernel_info_content());
            Ok(Some(reply.into_frames(key)))
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

            // Delegate rendering to the substrate-agnostic notebook core.
            let rendered = stratum_notebook::render_text(&code);

            if !silent {
                publish(
                    iopub,
                    key,
                    "stream",
                    &session,
                    msg.header.clone(),
                    json!({ "name": "stdout", "text": format!("{rendered}\n") }),
                )
                .await?;
                publish(
                    iopub,
                    key,
                    "execute_result",
                    &session,
                    msg.header.clone(),
                    json!({
                        "execution_count": count,
                        "data": { "text/plain": rendered },
                        "metadata": {},
                    }),
                )
                .await?;
            }

            let reply = reply_to(
                msg,
                "execute_reply",
                &session,
                json!({
                    "status": "ok",
                    "execution_count": count,
                    "user_expressions": {},
                    "payload": [],
                }),
            );
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
        // Unknown request types are ignored in Phase 0.
        _ => Ok(None),
    }
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

/// Build the `kernel_info_reply` content. Highlighting fields are placeholders
/// (`"text"`) in Phase 0; a real Pygments lexer / CodeMirror mode land later.
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
            "pygments_lexer": "text",
            "codemirror_mode": "text",
        },
        "banner": "Stratum kernel (Phase 0) — executable core for the πρσϕ-Formalism (reflective ρ-calculus). Cells are echoed back.",
        "help_links": [],
    })
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
