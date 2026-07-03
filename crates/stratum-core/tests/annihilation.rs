//! Pluggable synchronization (§2.8) — the `SyncRule` trait and its two instances.
//!
//! §2.8 leaves the *channel / co-channel* pairing a parameter of the calculus.
//! These tests pin down two readings:
//!
//! * [`NameEquiv`] must reproduce the default `Comm` rule (`≡N`) exactly, so
//!   every existing caller of the un-suffixed reducer is unaffected.
//! * [`Annihilation`] is a bounded under-approximation of the Comm-annihilation
//!   family: two channels pair up when their dropped processes robustly reduce
//!   to `0`. We check the paper's base case ("`0` is its own co-channel"), a
//!   pair that annihilates only after a reduction, a pair that does *not*
//!   annihilate, and a golden system that reduces under `Annihilation` but is
//!   stuck under `NameEquiv`.

use stratum_core::congruence::name_equiv;
use stratum_core::reduce::{
    step_labeled, step_labeled_with, step_with, Annihilation, NameEquiv, SyncRule,
};
use stratum_core::term::{drop_, input, lift, output, par, quote, zero, Name, Proc};

/// The reduction depth used throughout: generous enough for the one- and
/// two-step annihilations below, small enough to stay cheap.
const BOUND: usize = 4;

// ---------------------------------------------------------------------------
// NameEquiv reproduces the default reducer exactly.
// ---------------------------------------------------------------------------

/// On a handshake-style term, driving the reducer with `NameEquiv` yields the
/// very same labelled transitions as the un-suffixed [`step_labeled`] — element
/// for element, in order. This is the guarantee that making synchronization
/// pluggable did not perturb the default semantics.
#[test]
fn name_equiv_reproduces_default() {
    // x[z] | x(y).*y  with x = z = ⌜0⌝ — the §2.8 sugar handshake.
    let x = quote(zero());
    let sender = output(x.clone(), quote(zero()));
    let receiver = input(x, drop_);
    let handshake = par([sender, receiver]);

    assert_eq!(
        step_labeled_with(&handshake, &NameEquiv),
        step_labeled(&handshake),
        "NameEquiv must reproduce the default Comm rule exactly",
    );

    // Also on a nondeterministic term (one sender, two distinct receivers).
    let a = quote(zero());
    let r1 = input(a.clone(), |_| lift(quote(drop_(quote(zero()))), zero()));
    let r2 = input(a.clone(), |_| {
        lift(quote(output(quote(zero()), quote(zero()))), zero())
    });
    let branching = par([lift(a, zero()), r1, r2]);

    let via_trait = step_labeled_with(&branching, &NameEquiv);
    assert_eq!(via_trait, step_labeled(&branching));
    assert_eq!(via_trait.len(), 2, "one transition per receiver");
}

// ---------------------------------------------------------------------------
// Annihilation: what synchronizes and what does not.
// ---------------------------------------------------------------------------

/// The paper's base case: `0` is its own co-channel. With `x0 = x1 = ⌜0⌝`,
/// dropping runs the quoted `0`, so `*⌜0⌝ | *⌜0⌝ ≡ 0` — annihilation holds in
/// zero reduction steps (so even `bound = 0` accepts it).
#[test]
fn annihilation_base_case_zero_is_its_own_co_channel() {
    let zero_chan = quote(zero()); // ⌜0⌝
    assert!(Annihilation { bound: 0 }.synchronize(&zero_chan, &zero_chan));
    assert!(Annihilation { bound: BOUND }.synchronize(&zero_chan, &zero_chan));
}

/// A pair that annihilates only *after* a reduction: `x0 = ⌜a(y).0⌝` and
/// `x1 = ⌜a⟨|0|⟩⌝` (with `a = ⌜0⌝`). Their drops are `a(y).0` and `a⟨|0|⟩`,
/// which Comm-react on `a` to `0`. This is *not* accepted by `≡N` — the quoted
/// input and quoted lift are structurally distinct — so it is a genuine
/// Annihilation-only synchronization.
#[test]
fn annihilation_fires_after_reduction() {
    let a = quote(zero());
    let x0 = quote(input(a.clone(), |_| zero())); // ⌜a(y).0⌝
    let x1 = quote(lift(a, zero())); // ⌜a⟨|0|⟩⌝

    assert!(!name_equiv(&x0, &x1), "the two channels are NOT ≡N");
    assert!(
        Annihilation { bound: BOUND }.synchronize(&x0, &x1),
        "their drops a(y).0 | a⟨|0|⟩ reduce to 0",
    );
    // Symmetric.
    assert!(Annihilation { bound: BOUND }.synchronize(&x1, &x0));
}

/// A pair that does NOT annihilate: `x0 = x1 = ⌜a⟨|0|⟩⌝`. Their drops are two
/// parallel senders `a⟨|0|⟩ | a⟨|0|⟩` with no receiver — an irreducible normal
/// form that is not `0`. Yet these channels *are* `≡N` (they are identical), so
/// `NameEquiv` and `Annihilation` disagree here.
#[test]
fn annihilation_rejects_stuck_pair_where_name_equiv_accepts() {
    let a = quote(zero());
    let sender_chan = quote(lift(a, zero())); // ⌜a⟨|0|⟩⌝

    assert!(name_equiv(&sender_chan, &sender_chan), "identical ⇒ ≡N");
    assert!(
        !Annihilation { bound: BOUND }.synchronize(&sender_chan, &sender_chan),
        "two parallel senders never reach 0",
    );
}

/// Robustness: a pair whose drop reaches `0` but can also get stuck at a
/// non-`0` normal form must be rejected. `x0 = ⌜a(y).0⌝`, `x1 = ⌜a⟨|0|⟩ | b⟨|0|⟩⌝`
/// (with `a = ⌜0⌝`, `b = ⌜*⌜0⌝⌝` distinct): the `a` handshake fires but the
/// stray sender `b⟨|0|⟩` is left behind, so the only normal form is `b⟨|0|⟩ ≠ 0`.
#[test]
fn annihilation_requires_robust_reduction_to_zero() {
    let a = quote(zero());
    // ⌜⌜0⌝⟨|0|⟩⌝ — a quoted *lift*, so quote-drop does not collapse it to a; a ≠N b.
    let b = quote(lift(quote(zero()), zero()));
    assert!(!name_equiv(&a, &b));

    let x0 = quote(input(a.clone(), |_| zero())); // ⌜a(y).0⌝
    let x1 = quote(par([lift(a, zero()), lift(b, zero())])); // ⌜a⟨|0|⟩ | b⟨|0|⟩⌝

    assert!(
        !Annihilation { bound: BOUND }.synchronize(&x0, &x1),
        "a stray sender survives ⇒ no robust annihilation to 0",
    );
}

/// Regression (truncation soundness): a candidate `*x0 | *x1` with one
/// interleaving that reaches `0` within the bound **and** another interleaving
/// that stays live past the bound must NOT be reported as annihilating.
///
/// Construction — a payload race on channel `a = ⌜0⌝` with two senders and two
/// receivers:
///
/// ```text
/// *x0 = a⟨|0|⟩ | a(x).*x        *x1 = a⟨|D|⟩ | a(x).0
/// ```
///
/// where `D` is a divergent process on a distinct channel `c` (a derived
/// replicator `!0`, which unfolds forever and never reaches a normal form).
/// Two matchings exist:
///   * `a⟨|0|⟩↔a(x).*x` (runs `0`) with `a⟨|D|⟩↔a(x).0` (discards `D`) → `0`,
///     reached in two steps;
///   * `a⟨|0|⟩↔a(x).0` with `a⟨|D|⟩↔a(x).*x` (runs `D`) → `D`, which diverges.
///
/// With `bound = 3` the first run reaches `0` while the second is still reducible
/// on the frontier — and `D` never yields a non-`0` normal form, so the *old*
/// code (which only rejected on a reachable non-`0` normal form) wrongly returned
/// `true`. The truncation guard makes this a correct `false`.
#[test]
fn annihilation_rejects_truncated_race_reaching_zero_on_one_path_only() {
    // `D(c) = c(y).(c[y] | *y)` — the §3 replicator.
    fn replicator(c: Name) -> Proc {
        input(c.clone(), move |y| {
            par([output(c.clone(), y.clone()), drop_(y)])
        })
    }
    // `!0 on c = c⟨|D(c)|0|⟩ | D(c)` — unfolds forever (never a normal form).
    fn divergent(c: Name) -> Proc {
        par([
            lift(c.clone(), par([replicator(c.clone()), zero()])),
            replicator(c),
        ])
    }

    let a = quote(zero()); // ⌜0⌝
                           // c ≠N a: a quoted *lift*, immune to the ⌜*x⌝ ≡N x quote-drop collapse.
    let c = quote(lift(quote(zero()), zero()));
    assert!(!name_equiv(&a, &c));

    // *x0 = a⟨|0|⟩ | a(x).*x      (the *x receiver runs whatever it gets)
    let x0 = quote(par([lift(a.clone(), zero()), input(a.clone(), drop_)]));
    // *x1 = a⟨|D|⟩ | a(x).0        (the sender carries the divergent payload)
    let x1 = quote(par([lift(a.clone(), divergent(c)), input(a, |_| zero())]));

    // bound = 3: enough for the 0-run (2 steps), while the D-run is still live.
    assert!(
        !Annihilation { bound: 3 }.synchronize(&x0, &x1),
        "a within-bound run to 0 does not license annihilation while another \
         run is still reducible at the bound",
    );
}

// ---------------------------------------------------------------------------
// Golden: a system reduces under Annihilation but is stuck under the default.
// ---------------------------------------------------------------------------

/// A whole redex that fires only under the Comm-annihilation family.
///
/// The system is `x0⟨|0|⟩ | x1(y).0` where the *outer* channels are
/// `x0 = ⌜a(y).0⌝` and `x1 = ⌜a⟨|0|⟩⌝`. Since `x0` and `x1` are not `≡N`, the
/// default reducer sees no redex and the term is in normal form. Under
/// `Annihilation`, the dropped channels `a(y).0` and `a⟨|0|⟩` annihilate, so the
/// outer Comm fires and the system reduces to `0`.
#[test]
fn golden_annihilation_reduces_where_default_is_stuck() {
    let a = quote(zero());
    let x0 = quote(input(a.clone(), |_| zero())); // ⌜a(y).0⌝
    let x1 = quote(lift(a, zero())); // ⌜a⟨|0|⟩⌝

    let sender = lift(x0, zero()); // x0⟨|0|⟩
    let receiver = input(x1, |_| zero()); // x1(y).0
    let system = par([sender, receiver]);

    // Default (≡N): stuck.
    assert!(
        step_with(&system, &NameEquiv).is_empty(),
        "the default reducer sees no redex (x0, x1 not ≡N)",
    );

    // Annihilation: fires, and the sole reduct is 0.
    let reducts = step_with(&system, &Annihilation { bound: BOUND });
    assert_eq!(
        reducts.len(),
        1,
        "the annihilation redex fires exactly once"
    );

    let canon: Vec<Proc> = reducts
        .iter()
        .map(stratum_core::congruence::canonicalize)
        .collect();
    assert_eq!(canon, vec![Proc::Zero], "x0⟨|0|⟩ | x1(y).0 → 0");

    // And this is a genuine difference from NameEquiv on the same term.
    assert_ne!(
        step_with(&system, &NameEquiv),
        step_with(&system, &Annihilation { bound: BOUND }),
    );
}

/// Sanity: `Annihilation` never invents redexes on a `≡N` handshake that the
/// default already fires — here both reduce the sugar handshake identically,
/// because the sender/receiver channels are literally equal (`⌜0⌝`), whose drops
/// (`0 | 0`) also annihilate.
#[test]
fn annihilation_agrees_with_default_on_zero_channel_handshake() {
    let x = quote(zero());
    let handshake = par([output(x.clone(), quote(zero())), input(x, drop_)]);

    let default = step_with(&handshake, &NameEquiv);
    let annih = step_with(&handshake, &Annihilation { bound: BOUND });
    assert_eq!(default.len(), 1);
    assert_eq!(annih.len(), 1);
    assert_eq!(
        stratum_core::congruence::canonicalize(&default[0]),
        stratum_core::congruence::canonicalize(&annih[0]),
    );
}
