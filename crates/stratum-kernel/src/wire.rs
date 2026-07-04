//! The Jupyter wire protocol: connection files, HMAC signing, and multipart
//! message framing.
//!
//! This module is transport-agnostic on purpose. It turns bytes ⇄ structured
//! [`Message`]s and computes/verifies signatures; the [`crate`] binary wires it
//! to ZeroMQ sockets. Getting the three moving parts exactly right — the
//! `<IDS|MSG>` delimiter, the HMAC over the four JSON blobs, and the header
//! shape — is the whole point of the Phase 0 skeleton.
//!
//! References: Jupyter "Messaging in Jupyter" spec, protocol version 5.3.

use hmac::{Hmac, Mac};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::Sha256;

type HmacSha256 = Hmac<Sha256>;

/// The delimiter frame that separates ZMQ routing identities from the signed
/// message payload.
pub const DELIMITER: &[u8] = b"<IDS|MSG>";

/// Jupyter messaging protocol version implemented by this kernel.
pub const PROTOCOL_VERSION: &str = "5.3";

/// The Jupyter connection file (JSON), whose path Jupyter passes as `argv` in
/// place of `{connection_file}`.
#[derive(Debug, Clone, Deserialize)]
pub struct ConnectionInfo {
    /// Transport protocol — `"tcp"` in practice.
    pub transport: String,
    /// Bind address, e.g. `"127.0.0.1"`.
    pub ip: String,
    /// Shared HMAC key. Empty string disables signing.
    #[serde(default)]
    pub key: String,
    /// Signature scheme, e.g. `"hmac-sha256"`.
    #[serde(default)]
    pub signature_scheme: String,
    pub shell_port: u16,
    pub iopub_port: u16,
    pub stdin_port: u16,
    pub control_port: u16,
    pub hb_port: u16,
}

impl ConnectionInfo {
    /// Build the ZeroMQ endpoint string for a given port.
    #[must_use]
    pub fn endpoint(&self, port: u16) -> String {
        format!("{}://{}:{}", self.transport, self.ip, port)
    }

    /// The signing key as bytes. An empty key means signing is disabled.
    #[must_use]
    pub fn key_bytes(&self) -> &[u8] {
        self.key.as_bytes()
    }

    /// Whether the connection requests a signature scheme this kernel implements.
    /// Only `hmac-sha256` (or an unset scheme) is supported in Phase 0.
    #[must_use]
    pub fn scheme_supported(&self) -> bool {
        self.signature_scheme.is_empty() || self.signature_scheme == "hmac-sha256"
    }
}

/// A message header (Jupyter protocol 5.3).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Header {
    pub msg_id: String,
    pub session: String,
    pub username: String,
    /// ISO-8601 UTC timestamp.
    pub date: String,
    pub msg_type: String,
    pub version: String,
}

impl Header {
    /// Create a fresh header for an outgoing message, inheriting `session` and
    /// `username` from a parent header when one is present (so replies carry the
    /// caller's session), and minting a new `msg_id` and timestamp.
    #[must_use]
    pub fn new(msg_type: &str, session: &str, username: &str) -> Self {
        Self {
            msg_id: uuid::Uuid::new_v4().to_string(),
            session: session.to_string(),
            username: username.to_string(),
            date: now_iso8601(),
            msg_type: msg_type.to_string(),
            version: PROTOCOL_VERSION.to_string(),
        }
    }
}

/// A parsed/decoded Jupyter message: the ZMQ routing identities plus the four
/// JSON blobs that get signed.
#[derive(Debug, Clone)]
pub struct Message {
    /// ZMQ routing identities (frames before the `<IDS|MSG>` delimiter).
    pub identities: Vec<Vec<u8>>,
    pub header: Value,
    /// Decoded for protocol fidelity; Phase 0 handlers key off `header`/`content`.
    #[allow(dead_code)]
    pub parent_header: Value,
    /// Decoded for protocol fidelity; unused by Phase 0 handlers.
    #[allow(dead_code)]
    pub metadata: Value,
    pub content: Value,
}

impl Message {
    /// The `msg_type` from the header, or `""` if absent/ill-typed.
    #[must_use]
    pub fn msg_type(&self) -> &str {
        self.header
            .get("msg_type")
            .and_then(Value::as_str)
            .unwrap_or("")
    }

    /// Parse a multipart frame list into a [`Message`], verifying the HMAC
    /// signature against `key`.
    ///
    /// Returns `Err` if the delimiter is missing, the frame count is short, the
    /// JSON is malformed, or (when `key` is non-empty) the signature does not
    /// verify. A bad signature therefore *cannot* be turned into a processable
    /// message — the rejection the acceptance test relies on.
    pub fn parse(frames: Vec<Vec<u8>>, key: &[u8]) -> Result<Self, WireError> {
        let idx = frames
            .iter()
            .position(|f| f.as_slice() == DELIMITER)
            .ok_or(WireError::MissingDelimiter)?;

        // After the delimiter: signature, header, parent_header, metadata,
        // content, then optional buffers (ignored in Phase 0).
        let rest = &frames[idx + 1..];
        if rest.len() < 5 {
            return Err(WireError::TooShort);
        }
        let signature = &rest[0];
        let header = &rest[1];
        let parent_header = &rest[2];
        let metadata = &rest[3];
        let content = &rest[4];

        if !verify(key, &[header, parent_header, metadata, content], signature) {
            return Err(WireError::BadSignature);
        }

        Ok(Self {
            identities: frames[..idx].to_vec(),
            header: parse_json(header)?,
            parent_header: parse_json(parent_header)?,
            metadata: parse_json(metadata)?,
            content: parse_json(content)?,
        })
    }
}

/// A reply/broadcast to be serialized and signed for the wire.
///
/// `identities` are the ZMQ routing frames: for ROUTER replies (shell/control)
/// these are the request's identities so the peer is addressed; for a PUB
/// (iopub) broadcast this is the topic frame(s).
pub struct Outgoing {
    pub identities: Vec<Vec<u8>>,
    pub header: Header,
    pub parent_header: Value,
    pub metadata: Value,
    pub content: Value,
}

impl Outgoing {
    /// Serialize to signed multipart frames ready to hand to a ZMQ socket.
    #[must_use]
    pub fn into_frames(self, key: &[u8]) -> Vec<Vec<u8>> {
        let header = serde_json::to_vec(&self.header).expect("header serializes");
        let parent = serde_json::to_vec(&self.parent_header).expect("parent serializes");
        let metadata = serde_json::to_vec(&self.metadata).expect("metadata serializes");
        let content = serde_json::to_vec(&self.content).expect("content serializes");

        let signature = sign(key, &[&header, &parent, &metadata, &content]);

        let mut frames = self.identities;
        frames.push(DELIMITER.to_vec());
        frames.push(signature.into_bytes());
        frames.push(header);
        frames.push(parent);
        frames.push(metadata);
        frames.push(content);
        frames
    }
}

/// Compute the hex HMAC-SHA256 signature over the concatenation of the JSON
/// blobs (header|parent_header|metadata|content). An empty key disables signing
/// and yields an empty signature.
#[must_use]
pub fn sign(key: &[u8], parts: &[&[u8]]) -> String {
    if key.is_empty() {
        return String::new();
    }
    let mut mac = HmacSha256::new_from_slice(key).expect("HMAC accepts any key length");
    for part in parts {
        mac.update(part);
    }
    hex::encode(mac.finalize().into_bytes())
}

/// Verify a hex signature over the JSON blobs. Empty key ⇒ signing disabled ⇒
/// always accept. Uses the MAC's constant-time verification.
#[must_use]
pub fn verify(key: &[u8], parts: &[&[u8]], signature_hex: &[u8]) -> bool {
    if key.is_empty() {
        return true;
    }
    let expected = match hex::decode(signature_hex) {
        Ok(bytes) => bytes,
        Err(_) => return false,
    };
    let mut mac = HmacSha256::new_from_slice(key).expect("HMAC accepts any key length");
    for part in parts {
        mac.update(part);
    }
    mac.verify_slice(&expected).is_ok()
}

/// ISO-8601 UTC timestamp, e.g. `2026-07-04T12:34:56.789Z`.
#[must_use]
pub fn now_iso8601() -> String {
    chrono::Utc::now().to_rfc3339_opts(chrono::SecondsFormat::Millis, true)
}

fn parse_json(bytes: &[u8]) -> Result<Value, WireError> {
    // Jupyter uses `{}` for empty parent_header/metadata; tolerate empty frames.
    if bytes.is_empty() {
        return Ok(json!({}));
    }
    serde_json::from_slice(bytes).map_err(|_| WireError::BadJson)
}

/// Errors from decoding an incoming wire message.
#[derive(Debug)]
pub enum WireError {
    MissingDelimiter,
    TooShort,
    BadSignature,
    BadJson,
}

impl std::fmt::Display for WireError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = match self {
            WireError::MissingDelimiter => "missing <IDS|MSG> delimiter",
            WireError::TooShort => "too few frames after delimiter",
            WireError::BadSignature => "HMAC signature verification failed",
            WireError::BadJson => "malformed JSON in a message blob",
        };
        f.write_str(s)
    }
}

impl std::error::Error for WireError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sign_then_verify_roundtrips() {
        let key = b"secret-key";
        let parts: [&[u8]; 4] = [b"h", b"p", b"m", b"c"];
        let sig = sign(key, &parts);
        assert!(verify(key, &parts, sig.as_bytes()));
        // Tampered content fails.
        let bad: [&[u8]; 4] = [b"h", b"p", b"m", b"X"];
        assert!(!verify(key, &bad, sig.as_bytes()));
    }

    #[test]
    fn empty_key_disables_signing() {
        let key = b"";
        let parts: [&[u8]; 4] = [b"h", b"p", b"m", b"c"];
        assert_eq!(sign(key, &parts), "");
        assert!(verify(key, &parts, b""));
    }

    #[test]
    fn parse_rejects_bad_signature() {
        let key = b"k";
        let out = Outgoing {
            identities: vec![b"id".to_vec()],
            header: Header::new("kernel_info_request", "s", "u"),
            parent_header: json!({}),
            metadata: json!({}),
            content: json!({}),
        };
        let mut frames = out.into_frames(key);
        // Corrupt the signature frame (index: after identities + delimiter).
        let sig_pos = frames.iter().position(|f| f == DELIMITER).unwrap() + 1;
        frames[sig_pos] = b"deadbeef".to_vec();
        assert!(matches!(
            Message::parse(frames, key),
            Err(WireError::BadSignature)
        ));
    }

    #[test]
    fn parse_roundtrips_good_message() {
        let key = b"k";
        let out = Outgoing {
            identities: vec![b"id".to_vec()],
            header: Header::new("execute_request", "sess", "user"),
            parent_header: json!({}),
            metadata: json!({}),
            content: json!({"code": "1+1"}),
        };
        let frames = out.into_frames(key);
        let msg = Message::parse(frames, key).expect("valid message parses");
        assert_eq!(msg.msg_type(), "execute_request");
        assert_eq!(msg.content["code"], "1+1");
        assert_eq!(msg.identities, vec![b"id".to_vec()]);
    }
}
