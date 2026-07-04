# stratum-kernel

A [Jupyter](https://jupyter.org/) kernel for the **Stratum** DSL. It speaks the
Jupyter messaging protocol (v5.3) over **pure-Rust ZeroMQ** (the
[`zeromq`](https://crates.io/crates/zeromq) crate — no system `libzmq`, which
matters on Windows) and delegates all cell handling to the substrate-agnostic
[`stratum-notebook`](../stratum-notebook) core.

This is the **Phase 0 walking skeleton** (issue #37): it proves the wire
protocol end to end. It answers `kernel_info_request` and *echoes* the code in an
`execute_request` back as output. Language-aware evaluation, completion, and rich
rendering arrive in later phases inside `stratum-notebook`.

## What it implements

| Channel   | ZMQ socket | Handled messages                                   |
|-----------|------------|----------------------------------------------------|
| shell     | ROUTER     | `kernel_info_request`, `execute_request`           |
| control   | ROUTER     | `shutdown_request`, `interrupt_request`, `kernel_info_request` |
| iopub     | PUB        | `status` (busy/idle/starting), `execute_input`, `stream`, `execute_result` |
| stdin     | ROUTER     | (drained; no `input_request` flow yet)             |
| heartbeat | REP        | echoes bytes                                       |

- **Signing:** HMAC-SHA256 over `header|parent_header|metadata|content` (hex),
  keyed by the connection file's `key`. Every outgoing message is signed and
  every incoming message is verified; a bad signature is dropped, never
  processed. An empty key disables signing.
- **Framing:** `[identities…, "<IDS|MSG>", signature, header, parent_header,
  metadata, content, …buffers]`.

## Build

```sh
cargo build --release -p stratum-kernel
# binary at target/release/stratum-kernel[.exe]
```

## Install into Jupyter

The kernelspec in [`kernelspec/kernel.json`](kernelspec/kernel.json) uses a bare
`stratum-kernel` as `argv[0]`; the install script rewrites it to the absolute
path of the built binary.

```sh
# builds --release and registers the 'Stratum' kernel for the current user
./install.sh
```

Or manually:

```sh
cargo build --release -p stratum-kernel
# edit kernelspec/kernel.json so argv[0] is the absolute path to the binary, then:
jupyter kernelspec install --user --replace --name stratum crates/stratum-kernel/kernelspec
```

Verify it registered:

```sh
jupyter kernelspec list      # should list 'stratum'
```

## Manual verification (needs a real Jupyter)

1. `./install.sh`
2. `jupyter lab`
3. New Notebook → select the **Stratum** kernel.
4. In a cell type e.g. `new x in x!(*x)` and run it. You should see the code
   echoed back as the cell output (`execute_result` / stdout stream), the
   execution counter increments, and the kernel status dot goes busy → idle.
5. Kernel → Shut Down Kernel exits the process cleanly.

## Automated verification (no Jupyter required)

The integration test [`tests/protocol.rs`](tests/protocol.rs) *is* the acceptance
mechanism. It plays the role of a Jupyter frontend — spawns the built binary
against a temp connection file, connects DEALER/SUB/REQ clients, drives the
handshake + an execute cell, verifies HMAC signatures in both directions, asserts
a bad-signature message is rejected, and shuts down cleanly:

```sh
cargo test -p stratum-kernel
```
