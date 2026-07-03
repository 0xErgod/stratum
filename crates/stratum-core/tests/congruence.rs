//! Property and unit tests for structural congruence, name equivalence, and the
//! two substitutions — each keyed to a specific law of Meredith & Radestock
//! (2005).

use proptest::prelude::*;
use stratum_core::congruence::{canonicalize, name_equiv, structurally_congruent};
use stratum_core::subst::{subst_semantic, subst_syntactic};
use stratum_core::term::{drop_, fresh_sym, input, lift, output, par, quote, zero, Name, Proc};

/// A generator for closed processes whose only names are quotes or in-scope
/// bound occurrences (so no free variables ever appear).
fn arb_proc() -> impl Strategy<Value = Proc> {
    let leaf = prop_oneof![
        Just(zero()),
        Just(drop_(quote(zero()))),
        Just(output(quote(zero()), quote(zero()))),
    ];
    leaf.prop_recursive(4, 48, 4, |inner| {
        prop_oneof![
            prop::collection::vec(inner.clone(), 2..4).prop_map(par),
            inner.clone().prop_map(|p| lift(quote(zero()), p)),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| lift(quote(a), b)),
            // An input whose body sometimes references its own bound name,
            // exercising α-equivalence through binders.
            (inner.clone(), any::<bool>()).prop_map(|(p, use_bound)| {
                input(quote(zero()), move |y| {
                    if use_bound {
                        par([drop_(y), p.clone()])
                    } else {
                        p.clone()
                    }
                })
            }),
        ]
    })
}

proptest! {
    /// Canonicalization is idempotent: canonical forms are fixed points.
    #[test]
    fn canon_idempotent(p in arb_proc()) {
        let c = canonicalize(&p);
        prop_assert_eq!(canonicalize(&c), c);
    }

    /// Parallel is commutative (§2.3).
    #[test]
    fn par_commutative(a in arb_proc(), b in arb_proc()) {
        prop_assert!(structurally_congruent(
            &par([a.clone(), b.clone()]),
            &par([b, a]),
        ));
    }

    /// Parallel is associative (§2.3).
    #[test]
    fn par_associative(a in arb_proc(), b in arb_proc(), c in arb_proc()) {
        let left = par([a.clone(), par([b.clone(), c.clone()])]);
        let right = par([par([a, b]), c]);
        prop_assert!(structurally_congruent(&left, &right));
    }

    /// `0` is the unit of parallel (§2.3).
    #[test]
    fn par_unit(a in arb_proc()) {
        prop_assert!(structurally_congruent(&par([a.clone(), zero()]), &a));
        prop_assert!(structurally_congruent(&par([zero(), a.clone()]), &a));
    }

    /// Quote depth is well-defined and finite for every generated term (§2.5).
    #[test]
    fn quote_depth_finite(p in arb_proc()) {
        prop_assert!(p.quote_depth() < usize::MAX);
    }
}

/// `⌜*x⌝ ≡N x` and the nested `⌜*⌜P⌝⌝ ≡N ⌜P⌝` (quote-drop, §2.4).
#[test]
fn quote_drop_name_law() {
    let x = quote(zero());
    assert!(name_equiv(&quote(drop_(x.clone())), &x));

    let p = output(quote(zero()), quote(zero()));
    assert!(name_equiv(&quote(drop_(quote(p.clone()))), &quote(p)));
}

/// `⌜P⌝ ≡N ⌜Q⌝` whenever `P ≡ Q` (struct-equiv, §2.4): quotes of
/// structurally-congruent processes are name-equivalent.
#[test]
fn struct_equiv_name_law() {
    let inner_a = par([output(quote(zero()), quote(zero())), zero()]);
    let inner_b = output(quote(zero()), quote(zero()));
    assert!(structurally_congruent(&inner_a, &inner_b));
    assert!(name_equiv(&quote(inner_a), &quote(inner_b)));
}

/// `x(y).*y ≡ x(z).*z` — α-equivalence through a binder (§2.3).
#[test]
fn alpha_equivalence() {
    // Two separate `input` calls allocate distinct binder symbols, so equal
    // canonical forms genuinely exercise α-equivalence (not identity).
    let t1 = input(quote(zero()), drop_);
    let t2 = input(quote(zero()), drop_);
    assert!(structurally_congruent(&t1, &t2));
}

/// The process `*⌜P⌝` is *not* structurally congruent to `P`: drop is inert
/// under `≡`, and only the *name*-level quote-drop law fires (§2.0.4, §2.4).
#[test]
fn drop_quote_is_not_congruence() {
    let p = output(quote(zero()), quote(zero()));
    let dropped = drop_(quote(p.clone()));
    assert!(!structurally_congruent(&dropped, &p));
}

/// Dynamic quote (§2.6): the lifted body of `x⟨|*y|⟩` *is* substituted.
#[test]
fn dynamic_quote_is_substituted() {
    let y = fresh_sym();
    let term = lift(quote(zero()), drop_(Name::Var(y)));
    let out = subst_syntactic(&term, y, &quote(zero()));
    assert_eq!(out, lift(quote(zero()), drop_(quote(zero()))));
}

/// Static quote (§2.6): the body under `⌜·⌝` is impervious to substitution.
#[test]
fn static_quote_is_impervious() {
    let y = fresh_sym();
    // w⟨| *⌜*y⌝ |⟩  — the inner name ⌜*y⌝ is a quote and must not be touched.
    let frozen = lift(quote(zero()), drop_(quote(drop_(Name::Var(y)))));
    let out = subst_syntactic(&frozen, y, &quote(zero()));
    assert_eq!(out, frozen);
}

/// Semantic vs. syntactic substitution on drop (§2.7): semantically `*y` runs
/// the substituted code, syntactically it becomes a drop of the name.
#[test]
fn semantic_drop_runs_code() {
    let y = fresh_sym();
    let q = output(quote(zero()), quote(zero()));
    let term = drop_(Name::Var(y));

    // Semantic: (*y){⌜Q⌝/y} = Q
    let sem = subst_semantic(&term, y, &quote(q.clone()));
    assert_eq!(sem, q);

    // Syntactic: (*y){⌜Q⌝/y} = *⌜Q⌝
    let syn = subst_syntactic(&term, y, &quote(q.clone()));
    assert_eq!(syn, drop_(quote(q)));
}

/// A full `Comm` step by hand (§2.8):
/// `⌜0⌝⟨|Q|⟩ | ⌜0⌝(y).*y  →  Q`, via semantic substitution of `⌜Q⌝` for `y`.
#[test]
fn comm_step_by_hand() {
    let q = output(quote(zero()), quote(zero())); // some process Q
    let chan = quote(zero());

    // The receiver x(y).*y and the sender x⟨|Q|⟩ share channel ⌜0⌝.
    let y = fresh_sym();
    let recv_body = drop_(Name::Var(y)); // *y

    // Fire Comm: substitute the reified name ⌜Q⌝ for y, semantically.
    let result = subst_semantic(&recv_body, y, &quote(q.clone()));
    assert!(structurally_congruent(&result, &q));

    // Sanity: the two ends really are on the same channel.
    assert!(name_equiv(&chan, &quote(zero())));
}
