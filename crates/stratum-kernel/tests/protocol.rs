//! End-to-end acceptance test for the Jupyter wire protocol.
//!
//! This test plays the role of a Jupyter frontend so the kernel can be validated
//! **without a real Jupyter install**. It:
//!
//! 1. picks free localhost ports and writes a temp connection file with a known
//!    HMAC key,
//! 2. spawns the built `stratum-kernel` binary pointed at that file,
//! 3. connects as a client (DEALER→shell, SUB→iopub, REQ→heartbeat) using the
//!    same pure-Rust `zeromq` transport,
//! 4. drives the handshake and an execute cell, verifying HMAC signatures in
//!    both directions,
//! 5. asserts that a **bad-signature** message is rejected, and
//! 6. shuts the kernel down cleanly.
//!
//! Everything is wrapped in timeouts so a protocol bug fails fast instead of
//! hanging CI.

use std::net::TcpListener;
use std::process::{Child, Command};
use std::time::Duration;

use bytes::Bytes;
use hmac::{Hmac, Mac};
use serde_json::{json, Value};
use sha2::Sha256;
use tokio::time::timeout;
use zeromq::{DealerSocket, ReqSocket, Socket, SocketRecv, SocketSend, SubSocket, ZmqMessage};

type HmacSha256 = Hmac<Sha256>;

const KEY: &[u8] = b"a-shared-secret-key-for-tests";
const DELIMITER: &[u8] = b"<IDS|MSG>";
const RECV_TIMEOUT: Duration = Duration::from_secs(10);

/// Grab an OS-assigned free TCP port by binding and immediately dropping.
fn free_port() -> u16 {
    TcpListener::bind("127.0.0.1:0")
        .unwrap()
        .local_addr()
        .unwrap()
        .port()
}

fn sign(parts: &[&[u8]]) -> String {
    let mut mac = HmacSha256::new_from_slice(KEY).unwrap();
    for p in parts {
        mac.update(p);
    }
    hex::encode(mac.finalize().into_bytes())
}

/// A minimal frontend-side message builder mirroring the kernel's framing.
struct Frontend {
    session: String,
}

impl Frontend {
    fn header(&self, msg_type: &str) -> Value {
        json!({
            "msg_id": uuid::Uuid::new_v4().to_string(),
            "session": self.session,
            "username": "tester",
            "date": "2026-07-04T00:00:00.000Z",
            "msg_type": msg_type,
            "version": "5.3",
        })
    }

    /// Build signed frames for a request (no ZMQ identity — DEALER supplies it).
    fn request(&self, msg_type: &str, content: Value) -> Vec<Bytes> {
        self.request_with_sig(msg_type, content, None)
    }

    /// Like [`request`], but allows forcing a (bad) signature for the rejection
    /// test.
    fn request_with_sig(
        &self,
        msg_type: &str,
        content: Value,
        forced_sig: Option<&str>,
    ) -> Vec<Bytes> {
        let header = serde_json::to_vec(&self.header(msg_type)).unwrap();
        let parent = serde_json::to_vec(&json!({})).unwrap();
        let metadata = serde_json::to_vec(&json!({})).unwrap();
        let content = serde_json::to_vec(&content).unwrap();
        let signature = match forced_sig {
            Some(s) => s.to_string(),
            None => sign(&[&header, &parent, &metadata, &content]),
        };
        vec![
            Bytes::from_static(DELIMITER),
            Bytes::from(signature.into_bytes()),
            Bytes::from(header),
            Bytes::from(parent),
            Bytes::from(metadata),
            Bytes::from(content),
        ]
    }
}

/// A decoded reply: the four JSON blobs plus verification that the signature the
/// kernel produced is valid.
#[derive(Clone)]
struct Decoded {
    header: Value,
    parent_header: Value,
    content: Value,
}

/// Split a received multipart message at the delimiter and verify the kernel's
/// signature over the four JSON blobs.
fn decode_verified(msg: ZmqMessage) -> Decoded {
    let frames: Vec<Bytes> = msg.into_vec();
    let idx = frames
        .iter()
        .position(|f| f.as_ref() == DELIMITER)
        .expect("reply has <IDS|MSG> delimiter");
    let rest = &frames[idx + 1..];
    assert!(rest.len() >= 5, "reply has signature + 4 blobs");
    let signature = &rest[0];
    let header = &rest[1];
    let parent = &rest[2];
    let metadata = &rest[3];
    let content = &rest[4];

    // Verify the kernel signed its reply correctly.
    let expected = sign(&[header, parent, metadata, content]);
    assert_eq!(
        expected.as_bytes(),
        signature.as_ref(),
        "kernel reply signature must verify"
    );

    Decoded {
        header: serde_json::from_slice(header).unwrap(),
        parent_header: serde_json::from_slice(parent).unwrap(),
        content: serde_json::from_slice(content).unwrap(),
    }
}

/// Send an `execute_request` and collect every iopub message parented to it up
/// to and including the terminal `idle` status, then read the shell reply.
/// Returns `(reply, iopub_messages)`.
async fn execute(
    shell: &mut DealerSocket,
    iopub: &mut SubSocket,
    fe: &Frontend,
    code: &str,
    silent: bool,
) -> (Decoded, Vec<Decoded>) {
    let req = fe.request("execute_request", json!({ "code": code, "silent": silent }));
    let id = req_msg_id(&req);
    shell
        .send(ZmqMessage::try_from(req).unwrap())
        .await
        .unwrap();

    let mut msgs = Vec::new();
    timeout(RECV_TIMEOUT, async {
        loop {
            let m = decode_verified(recv(iopub).await);
            if m.parent_header["msg_id"] != Value::String(id.clone()) {
                continue; // stray startup/other message
            }
            let is_idle =
                m.header["msg_type"] == "status" && m.content["execution_state"] == "idle";
            msgs.push(m);
            if is_idle {
                break;
            }
        }
    })
    .await
    .expect("did not observe idle on iopub — kernel likely hung");

    let reply = decode_verified(recv(shell).await);
    assert_eq!(reply.header["msg_type"], "execute_reply");
    assert_eq!(reply.parent_header["msg_id"], Value::String(id));
    (reply, msgs)
}

/// Whether the collected iopub messages contain both a `busy` and an `idle`
/// status broadcast.
fn saw_busy_idle(msgs: &[Decoded]) -> bool {
    let busy = msgs
        .iter()
        .any(|m| m.header["msg_type"] == "status" && m.content["execution_state"] == "busy");
    let idle = msgs
        .iter()
        .any(|m| m.header["msg_type"] == "status" && m.content["execution_state"] == "idle");
    busy && idle
}

async fn recv(sock: &mut impl SocketRecv) -> ZmqMessage {
    timeout(RECV_TIMEOUT, sock.recv())
        .await
        .expect("recv timed out — kernel likely hung or misframed")
        .expect("recv error")
}

/// Spawn the kernel binary against a fresh connection file. Returns the child
/// and the connection info the frontend needs.
fn spawn_kernel() -> (Child, ConnPorts) {
    let ports = ConnPorts {
        shell: free_port(),
        iopub: free_port(),
        stdin: free_port(),
        control: free_port(),
        hb: free_port(),
    };
    let conn = json!({
        "transport": "tcp",
        "ip": "127.0.0.1",
        "key": String::from_utf8(KEY.to_vec()).unwrap(),
        "signature_scheme": "hmac-sha256",
        "shell_port": ports.shell,
        "iopub_port": ports.iopub,
        "stdin_port": ports.stdin,
        "control_port": ports.control,
        "hb_port": ports.hb,
        "kernel_name": "stratum",
    });
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("connection.json");
    std::fs::write(&path, serde_json::to_vec_pretty(&conn).unwrap()).unwrap();
    // Keep the tempdir alive for the child's lifetime by leaking it.
    std::mem::forget(dir);

    let child = Command::new(env!("CARGO_BIN_EXE_stratum-kernel"))
        .arg(&path)
        .spawn()
        .expect("spawn stratum-kernel");
    (child, ports)
}

struct ConnPorts {
    shell: u16,
    iopub: u16,
    stdin: u16,
    control: u16,
    hb: u16,
}

impl ConnPorts {
    fn ep(&self, port: u16) -> String {
        format!("tcp://127.0.0.1:{port}")
    }
}

#[tokio::test(flavor = "multi_thread", worker_threads = 2)]
async fn kernel_speaks_the_wire_protocol() {
    let (mut child, ports) = spawn_kernel();

    // Guard so the kernel is always killed even if an assertion panics.
    let result = tokio::spawn(drive(ports)).await;

    let _ = child.kill();
    let _ = child.wait();

    if let Err(e) = result {
        std::panic::resume_unwind(e.into_panic());
    }
}

async fn drive(ports: ConnPorts) {
    let fe = Frontend {
        session: uuid::Uuid::new_v4().to_string(),
    };

    // Connect the three client sockets. Retry connect briefly to let the kernel
    // finish binding.
    let mut shell = DealerSocket::new();
    connect_retry(&mut shell, &ports.ep(ports.shell)).await;
    let mut iopub = SubSocket::new();
    connect_retry(&mut iopub, &ports.ep(ports.iopub)).await;
    iopub.subscribe("").await.unwrap();
    let mut hb = ReqSocket::new();
    connect_retry(&mut hb, &ports.ep(ports.hb)).await;

    // Let the SUB subscription propagate before we trigger iopub traffic
    // (PUB/SUB slow-joiner).
    tokio::time::sleep(Duration::from_millis(400)).await;

    // ---- kernel_info_request -> kernel_info_reply -------------------------
    shell
        .send(ZmqMessage::try_from(fe.request("kernel_info_request", json!({}))).unwrap())
        .await
        .unwrap();
    let reply = decode_verified(recv(&mut shell).await);
    assert_eq!(reply.header["msg_type"], "kernel_info_reply");
    assert_eq!(reply.content["protocol_version"], "5.3");
    assert_eq!(reply.content["implementation"], "stratum");
    let li = &reply.content["language_info"];
    assert_eq!(li["name"], "stratum");
    assert_eq!(li["mimetype"], "text/x-stratum");
    assert_eq!(li["file_extension"], ".strat");

    // ---- execute a DSL cell -> display_data + execute_reply ---------------
    // A plain DSL cell defines a process into the session namespace and renders
    // the transparency pair as a display_data (text/plain + text/html).
    let (reply, io) = execute(&mut shell, &mut iopub, &fe, "new a\n\na!(0)", false).await;
    assert!(saw_busy_idle(&io), "missing busy/idle around the DSL cell");
    let display = io
        .iter()
        .find(|m| m.header["msg_type"] == "display_data")
        .expect("DSL cell must emit a display_data");
    assert!(
        display.content["data"]["text/plain"].as_str().is_some(),
        "display_data must carry text/plain"
    );
    assert_eq!(reply.header["msg_type"], "execute_reply");
    assert_eq!(reply.content["status"], "ok");
    assert_eq!(reply.content["execution_count"], 1);

    // ---- %explore -> display_data carrying image/svg+xml ------------------
    // Proves the wiring end to end: the notebook core lays the trace LTS out to
    // an inline SVG and the kernel forwards it under the image/svg+xml MIME key.
    let (reply, io) = execute(&mut shell, &mut iopub, &fe, "%explore _1 -> g", false).await;
    assert_eq!(reply.content["status"], "ok");
    assert_eq!(reply.content["execution_count"], 2);
    let svg_display = io
        .iter()
        .find(|m| {
            m.header["msg_type"] == "display_data"
                && m.content["data"]["image/svg+xml"].as_str().is_some()
        })
        .expect("%explore must emit a display_data with image/svg+xml");
    let svg = svg_display.content["data"]["image/svg+xml"]
        .as_str()
        .unwrap();
    assert!(svg.contains("<svg"), "not an SVG payload: {svg:.60}");

    // ---- a parse-error cell -> error reply + error broadcast --------------
    let (reply, io) = execute(&mut shell, &mut iopub, &fe, "new a in a!(", false).await;
    assert_eq!(reply.content["status"], "error", "parse error must fail");
    assert_eq!(reply.content["execution_count"], 3);
    assert_eq!(reply.content["ename"], "ParseError");
    assert!(
        io.iter().any(|m| m.header["msg_type"] == "error"),
        "parse-error cell must broadcast an iopub error"
    );

    // ---- complete_request -> complete_reply -------------------------------
    // `_1` and `g` are bound in the session by now (the DSL cell auto-named
    // `_1`, and `%explore ... -> g` bound the LTS). Completing `%exp` must
    // offer the directive names with a `%`-anchored replacement range.
    shell
        .send(
            ZmqMessage::try_from(fe.request(
                "complete_request",
                json!({ "code": "%exp", "cursor_pos": 4 }),
            ))
            .unwrap(),
        )
        .await
        .unwrap();
    let reply = decode_verified(recv(&mut shell).await);
    assert_eq!(reply.header["msg_type"], "complete_reply");
    assert_eq!(reply.content["status"], "ok");
    assert_eq!(reply.content["cursor_start"], 0);
    assert_eq!(reply.content["cursor_end"], 4);
    let matches: Vec<String> = reply.content["matches"]
        .as_array()
        .unwrap()
        .iter()
        .map(|m| m.as_str().unwrap().to_string())
        .collect();
    assert!(
        matches.contains(&"%explore".to_string()) && matches.contains(&"%expand".to_string()),
        "complete_reply must offer directive names, got {matches:?}"
    );

    // ---- inspect_request on a bound name -> inspect_reply{found:true} ------
    shell
        .send(
            ZmqMessage::try_from(fe.request(
                "inspect_request",
                json!({ "code": "g", "cursor_pos": 0, "detail_level": 0 }),
            ))
            .unwrap(),
        )
        .await
        .unwrap();
    let reply = decode_verified(recv(&mut shell).await);
    assert_eq!(reply.header["msg_type"], "inspect_reply");
    assert_eq!(reply.content["status"], "ok");
    assert_eq!(reply.content["found"], true, "`g` is a bound LTS");
    let plain = reply.content["data"]["text/plain"]
        .as_str()
        .expect("inspect_reply must carry text/plain");
    assert!(plain.contains("lts `g`"), "unexpected inspection: {plain}");

    // An unknown token -> found:false with empty data.
    shell
        .send(
            ZmqMessage::try_from(fe.request(
                "inspect_request",
                json!({ "code": "zzz_unbound", "cursor_pos": 2, "detail_level": 0 }),
            ))
            .unwrap(),
        )
        .await
        .unwrap();
    let reply = decode_verified(recv(&mut shell).await);
    assert_eq!(reply.header["msg_type"], "inspect_reply");
    assert_eq!(reply.content["found"], false);

    // ---- is_complete_request -> is_complete_reply -------------------------
    for (code, want) in [
        ("new a\na!(0)", "complete"),
        ("a(x).", "incomplete"),
        (")", "invalid"),
    ] {
        shell
            .send(
                ZmqMessage::try_from(fe.request("is_complete_request", json!({ "code": code })))
                    .unwrap(),
            )
            .await
            .unwrap();
        let reply = decode_verified(recv(&mut shell).await);
        assert_eq!(reply.header["msg_type"], "is_complete_reply");
        assert_eq!(
            reply.content["status"], want,
            "is_complete({code:?}) should be {want}"
        );
    }

    // ---- heartbeat echo ---------------------------------------------------
    hb.send(ZmqMessage::from(Bytes::from_static(b"ping")))
        .await
        .unwrap();
    let echo = recv(&mut hb).await;
    assert_eq!(echo.into_vec()[0].as_ref(), b"ping");

    // ---- bad-signature rejection -----------------------------------------
    // Send an execute with a deliberately wrong signature. The kernel must NOT
    // process it: no execute_reply comes back on shell.
    let bad = fe.request_with_sig(
        "execute_request",
        json!({ "code": "should be ignored", "silent": false }),
        Some("00000000000000000000000000000000"),
    );
    shell
        .send(ZmqMessage::try_from(bad).unwrap())
        .await
        .unwrap();
    // If the kernel wrongly processed it, an execute_reply would arrive. Expect
    // a timeout instead.
    let should_timeout = timeout(Duration::from_secs(2), shell.recv()).await;
    assert!(
        should_timeout.is_err(),
        "kernel must not reply to a bad-signature request"
    );

    // Prove the kernel is still alive and only rejected the bad one: a fresh,
    // correctly-signed request still gets a reply with the next execution_count.
    shell
        .send(
            ZmqMessage::try_from(fe.request(
                "execute_request",
                json!({ "code": "new c\n\nc!(0)", "silent": true }),
            ))
            .unwrap(),
        )
        .await
        .unwrap();
    let reply = decode_verified(recv(&mut shell).await);
    assert_eq!(reply.header["msg_type"], "execute_reply");
    assert_eq!(
        reply.content["execution_count"], 4,
        "count should advance to 4 (bad request never incremented it)"
    );

    // ---- clean shutdown via control --------------------------------------
    let mut control = DealerSocket::new();
    connect_retry(&mut control, &ports.ep(ports.control)).await;
    control
        .send(
            ZmqMessage::try_from(fe.request("shutdown_request", json!({ "restart": false })))
                .unwrap(),
        )
        .await
        .unwrap();
    let reply = decode_verified(recv(&mut control).await);
    assert_eq!(reply.header["msg_type"], "shutdown_reply");
    assert_eq!(reply.content["status"], "ok");
}

/// The `msg_id` embedded in a request's header frame (frame after signature).
fn req_msg_id(frames: &[Bytes]) -> String {
    let idx = frames.iter().position(|f| f.as_ref() == DELIMITER).unwrap();
    let header: Value = serde_json::from_slice(&frames[idx + 2]).unwrap();
    header["msg_id"].as_str().unwrap().to_string()
}

async fn connect_retry<S: Socket>(sock: &mut S, endpoint: &str) {
    for attempt in 0..50 {
        if sock.connect(endpoint).await.is_ok() {
            return;
        }
        tokio::time::sleep(Duration::from_millis(100)).await;
        if attempt == 49 {
            panic!("could not connect to {endpoint}");
        }
    }
}
