//! # Encodings — a standard library of derived ρ-calculus operators.
//!
//! Meredith & Radestock's §3 derives the *replication* and *restriction*
//! operators of the higher-order π-calculus **inside** the reflective calculus:
//! they are not primitive, but definable from the six core forms (`0`, input,
//! lift, drop, par, quote). Stratum honours that: the derived operators live in
//! *user space*, shipped here as inspectable [`stratum_syntax`] `def`-macros
//! rather than baked into the core.
//!
//! Each constant below is a fragment of `.strat` preamble. Prepend it to a
//! program (with [`with_stdlib`], or by hand) and the macro is in scope:
//!
//! ```
//! use stratum::encodings::with_stdlib;
//! use stratum::syntax::parse;
//!
//! // `bang(0)` — replicate the null process.
//! let src = with_stdlib("bang(0)");
//! assert!(parse(&src).is_ok());
//! ```
//!
//! Nothing here changes the calculus: [`stratum_syntax::expand`] desugars a use
//! site back to the raw §3 machinery (see [`BANG`]), and the result is an
//! ordinary closed [`stratum_core::Proc`]. The operators are *transparent*.
//!
//! ## `bang` — replication (§3)
//!
//! [`BANG`] is the paper's replication `!P`. Writing `B ≜ x(y).(x!(*y) | *y)`
//! for the self-replicating input, it is
//!
//! ```text
//! bang(P)  ≜  new x   x!( B | P ) | B
//! ```
//!
//! The single message `x!(B | P)` carries a *copy of the replicator together
//! with `P`*. Each time the co-located input `B` consumes it, `*y` unpacks that
//! copy — re-emitting the message (`x!(*y)`) and running `B | P` (`*y`) — so one
//! fresh `P` is spawned and the engine is restored:
//!
//! ```text
//! x!(B|P) | B  →  x!(B|P) | B | P  →  x!(B|P) | B | P | P  →  …
//! ```
//!
//! The channel `x` is minted by `new`, so it is *internal*: an observer that
//! does not watch `x` sees only the copies of `P` accumulate. This is exactly
//! the sense in which the replication machinery is unobservable — see the
//! correspondence checks in `crates/stratum/tests/encodings.rs` and the
//! `encodings` example.
//!
//! ## `contract` — input-guarded replication (§3)
//!
//! [`CONTRACT`] is `contract(C, P) ≜ bang( C(y).P )`: a *persistent* server on
//! channel `C`. Every message on `C` is received by one of the replicated
//! inputs and fires a fresh copy of the guarded body `P` (the received value
//! `y` is available to the guard but, being minted inside the macro, is not a
//! caller parameter — so `P` is run per message rather than over the payload).

/// Replication `!P` (§3): `bang(P) ≜ new x  x!(B | P) | B` with the
/// self-replicating input `B ≜ x(y).(x!(*y) | *y)`.
///
/// A `def`-macro fragment; prepend it to a program (see [`with_stdlib`]) and
/// call `bang(<some process>)`. `x` is minted fresh on every expansion, so
/// distinct `bang`s never share their internal channel (hygiene).
pub const BANG: &str =
    "def bang(P) { new x  x!( x(y).( x!(*y) | *y ) | P ) | x(y).( x!(*y) | *y ) }";

/// Input-guarded replication `!C(y).P` (§3): `contract(C, P) ≜ bang( C(y).P )`.
///
/// A persistent input on channel `C`: each message spawns a fresh copy of the
/// guarded body `P`. Requires [`BANG`] to be in scope (it is, when both come
/// from [`STDLIB`]).
pub const CONTRACT: &str = "def contract(C, P) { bang( C(y).P ) }";

/// The whole encodings standard library, ready to prepend to a program.
///
/// Currently [`BANG`] followed by [`CONTRACT`] (order matters: `contract`
/// expands through `bang`). Concatenated as `def` declarations, which the
/// surface syntax accepts as a preamble before the one program process.
pub const STDLIB: &str = concat!(
    "def bang(P) { new x  x!( x(y).( x!(*y) | *y ) | P ) | x(y).( x!(*y) | *y ) }",
    "\n",
    "def contract(C, P) { bang( C(y).P ) }",
    "\n",
);

/// Prepend the encodings [`STDLIB`] to a user program.
///
/// The returned source has the `def`-macros ([`BANG`], [`CONTRACT`], …) in
/// scope for `program`, ready to hand to [`stratum_syntax::parse`] or
/// [`stratum_syntax::expand`].
///
/// ```
/// use stratum::encodings::with_stdlib;
/// use stratum::syntax::{expand, parse};
///
/// let src = with_stdlib("bang(0)");
/// // Parses to an ordinary closed core term…
/// assert!(parse(&src).unwrap().is_closed());
/// // …and `expand` reveals the raw §3 machinery (no `def`/`new`/`bang` left).
/// let raw = expand(&src).unwrap();
/// assert!(!raw.contains("bang") && !raw.contains("def") && !raw.contains("new"));
/// ```
pub fn with_stdlib(program: &str) -> String {
    format!("{STDLIB}{program}")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::syntax::{expand, parse};

    #[test]
    fn stdlib_defs_are_the_named_constants() {
        // STDLIB is exactly the two shipped macros, in dependency order.
        assert!(STDLIB.contains(BANG));
        assert!(STDLIB.contains(CONTRACT));
    }

    #[test]
    fn with_stdlib_puts_macros_in_scope() {
        assert!(parse(&with_stdlib("bang(0)")).is_ok());
        assert!(parse(&with_stdlib("new c\ncontract(c, 0)")).is_ok());
    }

    #[test]
    fn expansion_is_transparent() {
        // No macro/def/new sugar survives desugaring.
        let raw = expand(&with_stdlib("bang(0)")).unwrap();
        assert!(!raw.contains("def"));
        assert!(!raw.contains("new"));
        assert!(!raw.contains("bang"));
    }
}
