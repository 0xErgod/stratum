//! The **checker**: the typing rules, the entry point [`check`], and the
//! reflective type-synthesis functions [`spatial_type`] / [`msg_type`].
//!
//! # The discipline
//!
//! A [channel-sort / behavioral][crate] discipline. A sort context Γ
//! ([`Env`](crate::Env)) says what each channel carries; a process is
//! *well-typed under Γ* when every send matches the receiver's expectation on
//! that channel. The judgment `Γ ⊢ P ok` is defined by:
//!
//! ```text
//!                                     Γ ⊢ P ok   Γ ⊢ Q ok
//! ───────────  (T-Zero)              ─────────────────────  (T-Par)
//!  Γ ⊢ 0 ok                              Γ ⊢ P | Q ok
//!
//!  carries(Γ, x) = T    Γ ⊢ ⌜Q⌝ : T    Γ ⊢ Q ok
//! ───────────────────────────────────────────────  (T-Lift)
//!               Γ ⊢ x⟨|Q|⟩ ok
//!
//!  carries(Γ, x) = T    Γ, y:T ⊢ P ok
//! ────────────────────────────────────  (T-Input)
//!            Γ ⊢ x(y).P ok
//! ```
//!
//! Two ingredients make this *reflective*, i.e. faithful to "names are quoted
//! processes":
//!
//! * **`Γ ⊢ ⌜Q⌝ : T`** (the payload check) does not consult a separate name
//!   sorting. The message a `Lift` transmits is the reified name `⌜Q⌝`, and its
//!   type is the **spatial type of the very process `Q` it quotes**
//!   ([`msg_type`] / [`spatial_type`]). So `⌜0⌝ : Nil`, `⌜x!(0)⌝ : Chan(Nil)`,
//!   and `⌜*y⌝` has whatever type `y` was received at (`⌜*y⌝ ≡N y`, §2.4).
//! * **`Γ ⊢ Q ok`** in T-Lift *recurses into the quoted carried process* — the
//!   code you put on the wire must itself type-check.
//!
//! Because a channel's own name and the messages it carries are typed by two
//! *different* judgments (Γ says what a channel carries; [`spatial_type`] says
//! what a name's code is), the self-referential names of the ρ-calculus type
//! cleanly: the handshake channel `req = ⌜0⌝` can carry `Nil` while the name
//! `⌜0⌝` also *is* a `Nil` message — no single-sort-per-name contradiction, and
//! no need for recursive sorts in this first cut.
//!
//! # Intended guarantee (communication safety)
//!
//! If `Γ ⊢ P ok` then in every reduction of `P`, whenever a lift on a channel
//! `x` meets an input on `x` (`≡N`), the transmitted name has exactly the type
//! the receiver bound its variable at. Hence a receiver never uses a received
//! name at a type its senders did not supply: no sender ever puts the "wrong
//! shape" on a channel. In particular a channel declared to carry `Nil` only
//! ever transmits `⌜0⌝`-typed messages. We do not mechanize subject reduction,
//! but the unit tests exercise **preservation** on concrete reductions
//! (including a substitution into a payload), which is the operational content
//! of that guarantee.
//!
//! # Protocol-theory connection (causality / measurability)
//!
//! A channel's carried type `T` is an upper bound on what an observer of that
//! channel can ever learn from a message: it fixes the *shape* every message
//! must have. This is the type-level shadow of `stratum-field`'s measurability —
//! a channel's type bounds the information legible at that channel, just as an
//! agent's field bounds what its observations can separate. Nested `Chan(_)`
//! types encode causal *depth*: a `Chan(Chan(Nil))` hands the receiver a fresh
//! channel to continue on, i.e. one further round of the protocol, so the type
//! records the causal ordering a session must follow.

use std::collections::HashMap;
use std::fmt;

use stratum_core::{Name, Proc};

use crate::ty::{Env, Ty};

/// A typing error, naming the offending channel and the expected-vs-got types.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeError {
    /// A name is used as a channel but no carried type is known for it: it is
    /// neither declared in Γ nor is its quoted code channel-shaped.
    UnsortedChannel {
        /// The offending channel name.
        chan: Name,
    },
    /// A name is used as a channel but its type is not a `Chan(_)` — e.g. a
    /// received name that only ever carries `Nil` is asked to carry a message.
    NotAChannel {
        /// The offending channel name.
        chan: Name,
        /// The (non-channel) type it actually has.
        got: Ty,
    },
    /// A `Lift` sends a payload of the wrong type on `chan`.
    PayloadMismatch {
        /// The channel the send happened on.
        chan: Name,
        /// The message type the channel carries.
        expected: Ty,
        /// The type of the payload actually sent.
        got: Ty,
    },
    /// A bound-name occurrence with no enclosing binder (an open term).
    UnboundName {
        /// The dangling binder symbol.
        sym: u64,
    },
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::UnsortedChannel { chan } => {
                write!(
                    f,
                    "unsorted channel `{}`: declare it in the context",
                    fmt_name(chan)
                )
            }
            TypeError::NotAChannel { chan, got } => write!(
                f,
                "name `{}` used as a channel but has non-channel type {got}",
                fmt_name(chan)
            ),
            TypeError::PayloadMismatch {
                chan,
                expected,
                got,
            } => write!(
                f,
                "payload mismatch on channel `{}`: expected {expected}, got {got}",
                fmt_name(chan)
            ),
            TypeError::UnboundName { sym } => write!(f, "unbound name x{sym} (open term)"),
        }
    }
}

impl std::error::Error for TypeError {}

/// A stack of in-scope binder types, keyed by binder symbol.
type Ctx = HashMap<u64, Ty>;

/// Check that `proc` is well-typed under the sort context `env` (`Γ ⊢ proc ok`).
///
/// Returns `Ok(())` on success, or the first [`TypeError`] found.
///
/// ```
/// use stratum_core::term::{input, lift, quote, zero};
/// use stratum_types::{check, Env, Ty};
///
/// // req = ⌜0⌝ carries Nil; `req!(0) | req(x).0` is well-typed.
/// let req = quote(zero());
/// let env = Env::new().with(req.clone(), Ty::Nil);
/// let p = stratum_core::par([
///     lift(req.clone(), zero()),
///     input(req, |_x| zero()),
/// ]);
/// assert!(check(&env, &p).is_ok());
/// ```
pub fn check(env: &Env, proc: &Proc) -> Result<(), TypeError> {
    let mut ctx = Ctx::new();
    check_proc(env, &mut ctx, proc)
}

fn check_proc(env: &Env, ctx: &mut Ctx, proc: &Proc) -> Result<(), TypeError> {
    match proc {
        Proc::Zero => Ok(()),
        Proc::Par(ps) => {
            for p in ps {
                check_proc(env, ctx, p)?;
            }
            Ok(())
        }
        // `*n` runs the code of `n`; any well-formed name is droppable. We still
        // resolve its message type so a dangling bound name is reported.
        Proc::Drop(n) => msg_type_ctx(env, ctx, n).map(|_| ()),
        Proc::Lift { chan, arg } => {
            let carried = channel_carries(env, ctx, chan)?;
            // The transmitted name is ⌜arg⌝; its type is the spatial type of the
            // process it quotes (reflective payload rule).
            let got = spatial_type_ctx(env, ctx, arg)?;
            if got != carried {
                return Err(TypeError::PayloadMismatch {
                    chan: chan.clone(),
                    expected: carried,
                    got,
                });
            }
            // The carried code must itself type-check (descend into the quote).
            check_proc(env, ctx, arg)
        }
        Proc::Input { chan, bound, body } => {
            let carried = channel_carries(env, ctx, chan)?;
            let shadowed = ctx.insert(*bound, carried);
            let result = check_proc(env, ctx, body);
            match shadowed {
                Some(prev) => {
                    ctx.insert(*bound, prev);
                }
                None => {
                    ctx.remove(bound);
                }
            }
            result
        }
    }
}

/// What messages `chan` carries, i.e. the `T` such that `chan : Chan(T)`.
///
/// A free channel (a quote) takes its carried type from Γ, falling back to its
/// reflected code if the quoted process is itself channel-shaped. A bound
/// channel (a received name) is a channel only if it was received at a `Chan(_)`
/// type.
fn channel_carries(env: &Env, ctx: &Ctx, chan: &Name) -> Result<Ty, TypeError> {
    match chan {
        Name::Var(sym) => match ctx.get(sym) {
            Some(Ty::Chan(t)) => Ok((**t).clone()),
            Some(other) => Err(TypeError::NotAChannel {
                chan: chan.clone(),
                got: other.clone(),
            }),
            None => Err(TypeError::UnboundName { sym: *sym }),
        },
        Name::Quote(p) => {
            if let Some(t) = env.carried(chan) {
                return Ok(t.clone());
            }
            // Reflective fallback: a channel whose code is itself an output/input
            // channel carries what that code carries.
            match spatial_type_ctx(env, ctx, p)? {
                Ty::Chan(t) => Ok(*t),
                _ => Err(TypeError::UnsortedChannel { chan: chan.clone() }),
            }
        }
    }
}

/// The **spatial / behavioral type** of a process (`Γ ⊢ P : T` for the process
/// grammar), computed reflectively.
///
/// This is the public, closed-term entry point (an empty binder context). It is
/// what gives a *name* its type: the type of `⌜P⌝` is `spatial_type(&env, &P)`.
///
/// ```
/// use stratum_core::term::{lift, quote, zero};
/// use stratum_types::{spatial_type, Env, Ty};
///
/// let env = Env::new();
/// // ⌜0⌝ : Nil
/// assert_eq!(spatial_type(&env, &zero()).unwrap(), Ty::Nil);
/// // ⌜ x!(0) ⌝ : Chan(Nil) — a name quoting "output 0 on x" is a channel of Nil.
/// let out = lift(quote(zero()), zero());
/// assert_eq!(spatial_type(&env, &out).unwrap(), Ty::chan(Ty::Nil));
/// ```
pub fn spatial_type(env: &Env, proc: &Proc) -> Result<Ty, TypeError> {
    let ctx = Ctx::new();
    spatial_type_ctx(env, &ctx, proc)
}

/// The **message type of a name** `Γ ⊢ n : T` — the type of the process `n`
/// quotes.
///
/// `⌜P⌝ : spatial_type(P)`; `⌜*x⌝ ≡N x`, so it takes the type of the process
/// `*x` runs, namely the drop's name; a bound occurrence `x` has the type it was
/// received at. Closed-term entry point (empty binder context).
pub fn msg_type(env: &Env, name: &Name) -> Result<Ty, TypeError> {
    let ctx = Ctx::new();
    msg_type_ctx(env, &ctx, name)
}

fn spatial_type_ctx(env: &Env, ctx: &Ctx, proc: &Proc) -> Result<Ty, TypeError> {
    match proc {
        Proc::Zero => Ok(Ty::Nil),
        // `*n` runs n's quoted code, so its type is n's message type.
        Proc::Drop(n) => msg_type_ctx(env, ctx, n),
        // A single output `x⟨|Q|⟩` is, spatially, a channel carrying Q's type.
        Proc::Lift { arg, .. } => Ok(Ty::chan(spatial_type_ctx(env, ctx, arg)?)),
        // Behavioral input types are not synthesized in this first cut.
        Proc::Input { .. } => Ok(Ty::Proc),
        Proc::Par(ps) => {
            // `0` is the unit; a lone non-nil component gives its type, and any
            // genuinely composite message is opaque (`Proc`).
            let mut non_nil = Vec::new();
            for p in ps {
                let t = spatial_type_ctx(env, ctx, p)?;
                if t != Ty::Nil {
                    non_nil.push(t);
                }
            }
            match non_nil.len() {
                0 => Ok(Ty::Nil),
                1 => Ok(non_nil.pop().unwrap()),
                _ => Ok(Ty::Proc),
            }
        }
    }
}

fn msg_type_ctx(env: &Env, ctx: &Ctx, name: &Name) -> Result<Ty, TypeError> {
    match name {
        Name::Var(sym) => ctx
            .get(sym)
            .cloned()
            .ok_or(TypeError::UnboundName { sym: *sym }),
        Name::Quote(p) => match &**p {
            // Quote-drop (§2.4): ⌜*x⌝ ≡N x, so it has x's message type.
            Proc::Drop(inner) => msg_type_ctx(env, ctx, inner),
            other => spatial_type_ctx(env, ctx, other),
        },
    }
}

// --- Minimal pretty-printer, so errors name channels legibly. ---

fn fmt_name(n: &Name) -> String {
    match n {
        Name::Var(s) => format!("x{s}"),
        Name::Quote(p) => format!("@{}", fmt_proc(p)),
    }
}

fn fmt_proc(p: &Proc) -> String {
    match p {
        Proc::Zero => "0".to_string(),
        Proc::Drop(n) => format!("*{}", fmt_name(n)),
        Proc::Lift { chan, arg } => format!("{}!({})", fmt_name(chan), fmt_proc(arg)),
        Proc::Input { chan, bound, body } => {
            format!("{}(x{bound}).{}", fmt_name(chan), fmt_proc(body))
        }
        Proc::Par(ps) => ps.iter().map(fmt_proc).collect::<Vec<_>>().join(" | "),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use stratum_core::term::{drop_, input, lift, output, par, quote, zero};
    use stratum_core::{step, Proc};

    /// req = ⌜0⌝, the handshake request channel.
    fn req() -> Name {
        quote(zero())
    }

    /// ack = ⌜ @0!(0) ⌝, the handshake acknowledge channel.
    fn ack() -> Name {
        quote(lift(quote(zero()), zero()))
    }

    fn handshake_env() -> Env {
        Env::new().with(req(), Ty::Nil).with(ack(), Ty::Nil)
    }

    #[test]
    fn handshake_is_well_typed() {
        // req!(0) | req(x).ack!(0)
        let p = par([lift(req(), zero()), input(req(), |_x| lift(ack(), zero()))]);
        assert!(check(&handshake_env(), &p).is_ok());
    }

    #[test]
    fn wrong_payload_shape_is_rejected() {
        // req!( c!(0) ) sends a Chan(Nil) message on a Nil-carrying channel.
        let c = quote(lift(quote(zero()), drop_(quote(zero()))));
        let p = par([lift(req(), lift(c, zero())), input(req(), |_x| zero())]);
        match check(&handshake_env(), &p) {
            Err(TypeError::PayloadMismatch { expected, got, .. }) => {
                assert_eq!(expected, Ty::Nil);
                assert_eq!(got, Ty::chan(Ty::Nil));
            }
            other => panic!("expected PayloadMismatch, got {other:?}"),
        }
    }

    #[test]
    fn using_a_nil_message_as_a_channel_is_rejected() {
        // req(x). x!(0)  — x was received at Nil, cannot be used as a channel.
        let p = input(req(), |x| lift(x, zero()));
        match check(&handshake_env(), &p) {
            Err(TypeError::NotAChannel { got, .. }) => assert_eq!(got, Ty::Nil),
            other => panic!("expected NotAChannel, got {other:?}"),
        }
    }

    #[test]
    fn received_channel_can_be_used_when_typed_as_chan() {
        // gate carries Chan(Nil): the received name may then send 0 on itself.
        // gate(x). x!(0)
        let gate = quote(lift(quote(zero()), zero())); // distinct from req/ack
        let env = Env::new().with(gate.clone(), Ty::chan(Ty::Nil));
        let p = input(gate, |x| lift(x, zero()));
        assert!(check(&env, &p).is_ok());
    }

    #[test]
    fn reflective_name_typing() {
        let env = Env::new();
        // The name ⌜0⌝ is a Nil message.
        assert_eq!(msg_type(&env, &quote(zero())).unwrap(), Ty::Nil);
        // ⌜*⌜0⌝⌝ ≡N ⌜0⌝, so also Nil (quote-drop).
        assert_eq!(
            msg_type(&env, &quote(drop_(quote(zero())))).unwrap(),
            Ty::Nil
        );
        // A name quoting an output is a channel.
        let out = lift(quote(zero()), zero());
        assert_eq!(msg_type(&env, &quote(out)).unwrap(), Ty::chan(Ty::Nil));
    }

    #[test]
    fn unsorted_channel_is_reported() {
        // req is undeclared here.
        let p = lift(req(), zero());
        match check(&Env::new(), &p) {
            Err(TypeError::UnsortedChannel { .. }) => {}
            other => panic!("expected UnsortedChannel, got {other:?}"),
        }
    }

    #[test]
    fn descends_into_the_carried_process() {
        // The payload `ack!( ack!(0) )` matches req's carried type at the top
        // (both are Chan(Chan(Nil))), yet is ill-typed *inside*: `ack` carries
        // Nil but is here made to carry `ack!(0)` : Chan(Nil). The T-Lift rule's
        // descent into the quoted carried code must catch this.
        let env = Env::new()
            .with(req(), Ty::chan(Ty::chan(Ty::Nil)))
            .with(ack(), Ty::Nil);
        // payload = ack!( ack!(0) ) : spatial type Chan(Chan(Nil)) = req's carried.
        let payload = lift(ack(), lift(ack(), zero()));
        let p = lift(req(), payload);
        match check(&env, &p) {
            Err(TypeError::PayloadMismatch { expected, got, .. }) => {
                assert_eq!(expected, Ty::Nil);
                assert_eq!(got, Ty::chan(Ty::Nil));
            }
            other => panic!("expected PayloadMismatch from descent, got {other:?}"),
        }
    }

    /// Subject reduction (preservation) on the plain handshake: the one reduct
    /// stays well-typed under the same Γ.
    #[test]
    fn preservation_plain_handshake() {
        let env = handshake_env();
        let p = par([lift(req(), zero()), input(req(), |_x| lift(ack(), zero()))]);
        assert!(check(&env, &p).is_ok());
        let succ = step(&p);
        assert!(!succ.is_empty(), "handshake should reduce");
        for q in &succ {
            assert!(
                check(&env, q).is_ok(),
                "reduct not well-typed: {}",
                fmt_proc(q)
            );
        }
    }

    /// Preservation across a substitution **into a payload**: the server
    /// forwards the received name on `ack`, and after the `Comm` the reduct
    /// `ack!(*⌜0⌝)` must still type-check.
    #[test]
    fn preservation_forwarding() {
        // req and ack both carry Nil; server forwards x on ack.
        let env = handshake_env();
        // req!(0) | req(x). ack!(*x)   [ack!(*x) = output(ack, x)]
        let p = par([lift(req(), zero()), input(req(), |x| output(ack(), x))]);
        assert!(check(&env, &p).is_ok(), "source should type-check");
        let succ: Vec<Proc> = step(&p);
        assert!(!succ.is_empty());
        for q in &succ {
            assert!(
                check(&env, q).is_ok(),
                "forwarded reduct not well-typed: {}",
                fmt_proc(q)
            );
        }
    }

    #[test]
    fn nested_channel_types_display() {
        assert_eq!(Ty::chan(Ty::chan(Ty::Nil)).to_string(), "Chan(Chan(Nil))");
    }
}
