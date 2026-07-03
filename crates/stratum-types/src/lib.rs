//! # stratum-types
//!
//! A **type-theory grain** for the reflective higher-order (ρ) calculus of
//! Meredith & Radestock — a first *channel-sort / behavioral* typing discipline
//! over [`stratum_core`], with a checker and examples. It is a tractable first
//! cut at the paper's forthcoming namespace-logic type system, not that system
//! in full.
//!
//! ## The idea, in one line
//!
//! Because **names are quoted processes**, a name can be typed by the *shape* of
//! the process it quotes; a channel can then be typed by the shape of what it
//! carries. That reflective move is the whole point, and it is realized directly
//! in the checker: the type of a payload `⌜Q⌝` is the *spatial type of `Q`*, and
//! sending it type-checks the code `Q` too.
//!
//! ## The discipline
//!
//! * The [type language](Ty) is `Nil | Chan(T) | Proc` — the null process, a
//!   channel carrying messages of type `T`, and an opaque top.
//! * A [sort context](Env) Γ assigns each **channel** (identified up to name
//!   equivalence `≡N`) the type of the messages it carries.
//! * [`check`] decides `Γ ⊢ P ok`: every `Lift{chan,arg}` sends an `arg` whose
//!   (reflected) type matches `chan`'s carried type and whose code type-checks;
//!   every `Input{chan,body}` binds the received name at `chan`'s carried type
//!   and checks `body`; `Zero`/`Par`/`Drop` compose the obvious way.
//! * [`spatial_type`] / [`msg_type`] expose the reflective synthesis: the type
//!   of a process, and hence of the name that quotes it.
//!
//! ## What well-typedness guarantees
//!
//! **Communication safety** (for the coherent sort contexts the checker
//! enforces): a receiver's expectation matches every sender on that channel, so
//! no reduction of an accepted program ever delivers a message of the wrong
//! shape — even when a received name is reused as a channel. To keep this sound,
//! [`check`] eagerly validates the whole context up front and rejects any entry
//! that contradicts a channel's own reflected code
//! ([`TypeError::IncoherentSort`]), so acceptance is closed under reduction.
//! Subject reduction is *argued and tested on
//! concrete reductions*, not mechanized as a proof. See [`check`] for the rules,
//! the precise guarantee, and the connection to `stratum-field` measurability (a
//! channel's type bounds what an observer of the channel can learn).
//!
//! ```
//! use stratum_core::term::{input, lift, quote, zero};
//! use stratum_core::par;
//! use stratum_types::{check, Env, Ty};
//!
//! // The handshake: req = ⌜0⌝ carries Nil; well-typed.
//! let req = quote(zero());
//! let ack = quote(lift(quote(zero()), zero()));
//! let env = Env::new()
//!     .with(req.clone(), Ty::Nil)
//!     .with(ack.clone(), Ty::Nil);
//! let protocol = par([
//!     lift(req.clone(), zero()),               // req!(0)
//!     input(req, move |_x| lift(ack, zero())), // req(x).ack!(0)
//! ]);
//! assert!(check(&env, &protocol).is_ok());
//! ```

pub mod check;
pub mod ty;

pub use check::{check, msg_type, spatial_type, TypeError};
pub use ty::{Env, Ty};
