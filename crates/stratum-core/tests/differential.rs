//! Differential test: an *independent* decision procedure for `≡`/`≡N`, checked
//! against `stratum_core`'s canonicalization on random terms.
//!
//! The library decides `≡` by **normalization**: canonical form (α → de Bruijn,
//! flatten parallel, *sort*) then compare. This reference decides `≡` by a
//! deliberately different method — **recursive bijection matching** over the
//! parallel components (no normal form, no sorting), rename-based α (no de
//! Bruijn), and peel-based `≡N`. Because the two share no strategy, a bug in one
//! is unlikely to be mirrored in the other: agreement across many random terms
//! is strong evidence they decide the same relation; any disagreement is a
//! concrete counterexample.
//!
//! Scope: this closes the *implementation*-fidelity gap (is canonicalization a
//! correct decision procedure for the relation we intend?). Both procedures
//! adopt the same modelling decision — `≡` absorbs `≡N` at name positions and
//! `*⌜P⌝` stays inert at the process level — so this does not re-litigate that
//! *specification* decision (that is the job of the paper golden tests).

use proptest::prelude::*;
use stratum_core::congruence::{name_equiv as lib_name_equiv, structurally_congruent};
use stratum_core::term::{drop_, fresh_sym, input, lift, output, par, quote, zero, Name, Proc};

// ---------------------------------------------------------------------------
// Independent reference implementation of ≡ and ≡N.
// ---------------------------------------------------------------------------
mod reference {
    use super::*;

    /// Flatten into active parallel components, dropping `0` and nested `Par`.
    fn components(p: &Proc, out: &mut Vec<Proc>) {
        match p {
            Proc::Zero => {}
            Proc::Par(ps) => ps.iter().for_each(|q| components(q, out)),
            other => out.push(other.clone()),
        }
    }

    /// α-rename: replace `Var(from)` with `Var(to)` everywhere, including under
    /// quotes. (Binder symbols are globally unique, so there is no capture.)
    fn rename_proc(p: &Proc, from: u64, to: u64) -> Proc {
        match p {
            Proc::Zero => Proc::Zero,
            Proc::Drop(n) => Proc::Drop(rename_name(n, from, to)),
            Proc::Lift { chan, arg } => Proc::Lift {
                chan: rename_name(chan, from, to),
                arg: Box::new(rename_proc(arg, from, to)),
            },
            Proc::Input { chan, bound, body } => Proc::Input {
                chan: rename_name(chan, from, to),
                bound: *bound,
                body: Box::new(rename_proc(body, from, to)),
            },
            Proc::Par(ps) => Proc::Par(ps.iter().map(|q| rename_proc(q, from, to)).collect()),
        }
    }

    fn rename_name(n: &Name, from: u64, to: u64) -> Name {
        match n {
            Name::Var(k) if *k == from => Name::Var(to),
            Name::Var(k) => Name::Var(*k),
            Name::Quote(p) => Name::Quote(Box::new(rename_proc(p, from, to))),
        }
    }

    /// If `p ≡ *x` for some name `x`, return that name. Since `*x` is a single
    /// non-`0` atom, any `p ≡ *x` is `*x` in parallel with units, so flattening
    /// and dropping `0`s is complete for this test.
    fn as_drop(p: &Proc) -> Option<Name> {
        let mut comps = Vec::new();
        components(p, &mut comps);
        if let [Proc::Drop(x)] = comps.as_slice() {
            Some(x.clone())
        } else {
            None
        }
    }

    /// Apply the quote-drop law `⌜*x⌝ ≡N x` at the head, up to `≡`.
    fn peel(n: Name) -> Name {
        match n {
            Name::Var(a) => Name::Var(a),
            Name::Quote(p) => match as_drop(&p) {
                Some(x) => peel(x),
                None => Name::Quote(p),
            },
        }
    }

    /// `m ≡N n` decided directly from §2.4: peel quote-drop, then compare —
    /// two variables by identity, two quotes by `≡` of their bodies.
    pub fn name_equiv(m: &Name, n: &Name) -> bool {
        match (peel(m.clone()), peel(n.clone())) {
            (Name::Var(a), Name::Var(b)) => a == b,
            (Name::Quote(p), Name::Quote(q)) => equiv(&p, &q),
            _ => false,
        }
    }

    /// Two active components are equivalent if they have the same shape and
    /// equivalent parts (bodies compared under a shared fresh binder for α).
    fn component_equiv(x: &Proc, y: &Proc) -> bool {
        match (x, y) {
            (Proc::Drop(m), Proc::Drop(n)) => name_equiv(m, n),
            (Proc::Lift { chan: c1, arg: a1 }, Proc::Lift { chan: c2, arg: a2 }) => {
                name_equiv(c1, c2) && equiv(a1, a2)
            }
            (
                Proc::Input {
                    chan: c1,
                    bound: b1,
                    body: body1,
                },
                Proc::Input {
                    chan: c2,
                    bound: b2,
                    body: body2,
                },
            ) => {
                if !name_equiv(c1, c2) {
                    return false;
                }
                let f = fresh_sym();
                equiv(&rename_proc(body1, *b1, f), &rename_proc(body2, *b2, f))
            }
            _ => false,
        }
    }

    /// Backtracking search for a perfect matching between two component lists.
    fn matches(ca: &[Proc], cb: &[Proc], used: &mut [bool], i: usize) -> bool {
        if i == ca.len() {
            return true;
        }
        for j in 0..cb.len() {
            if !used[j] && component_equiv(&ca[i], &cb[j]) {
                used[j] = true;
                if matches(ca, cb, used, i + 1) {
                    return true;
                }
                used[j] = false;
            }
        }
        false
    }

    /// `a ≡ b`: equal-size multisets of components with a component-wise
    /// equivalence-preserving bijection between them.
    pub fn equiv(a: &Proc, b: &Proc) -> bool {
        let mut ca = Vec::new();
        components(a, &mut ca);
        let mut cb = Vec::new();
        components(b, &mut cb);
        if ca.len() != cb.len() {
            return false;
        }
        let mut used = vec![false; cb.len()];
        matches(&ca, &cb, &mut used, 0)
    }
}

// ---------------------------------------------------------------------------
// Generators.
// ---------------------------------------------------------------------------
fn arb_proc() -> impl Strategy<Value = Proc> {
    let leaf = prop_oneof![
        Just(zero()),
        Just(drop_(quote(zero()))),
        Just(output(quote(zero()), quote(zero()))),
        Just(lift(quote(zero()), zero())),
    ];
    leaf.prop_recursive(4, 48, 4, |inner| {
        prop_oneof![
            prop::collection::vec(inner.clone(), 2..4).prop_map(par),
            inner.clone().prop_map(|p| lift(quote(zero()), p)),
            (inner.clone(), inner.clone()).prop_map(|(a, b)| lift(quote(a), b)),
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

/// A structurally-congruent variant of `p`, exercising every law: `0 ≡ 0|0`,
/// parallel reordering + extra units, α-renaming of every binder, and
/// struct-equiv under quotes.
fn congruent_variant(p: &Proc) -> Proc {
    match p {
        Proc::Zero => par([zero(), zero()]),
        Proc::Drop(n) => drop_(variant_name(n)),
        Proc::Lift { chan, arg } => lift(variant_name(chan), congruent_variant(arg)),
        Proc::Input { chan, bound, body } => {
            let f = fresh_sym();
            let renamed = rename_for_variant(body, *bound, f);
            Proc::Input {
                chan: variant_name(chan),
                bound: f,
                body: Box::new(congruent_variant(&renamed)),
            }
        }
        Proc::Par(ps) => {
            let mut v: Vec<Proc> = ps.iter().rev().map(congruent_variant).collect();
            v.push(zero());
            Proc::Par(v)
        }
    }
}

fn variant_name(n: &Name) -> Name {
    match n {
        Name::Var(k) => Name::Var(*k),
        Name::Quote(p) => quote(congruent_variant(p)),
    }
}

fn rename_for_variant(p: &Proc, from: u64, to: u64) -> Proc {
    match p {
        Proc::Zero => Proc::Zero,
        Proc::Drop(n) => Proc::Drop(rename_name_v(n, from, to)),
        Proc::Lift { chan, arg } => Proc::Lift {
            chan: rename_name_v(chan, from, to),
            arg: Box::new(rename_for_variant(arg, from, to)),
        },
        Proc::Input { chan, bound, body } => Proc::Input {
            chan: rename_name_v(chan, from, to),
            bound: *bound,
            body: Box::new(rename_for_variant(body, from, to)),
        },
        Proc::Par(ps) => Proc::Par(ps.iter().map(|q| rename_for_variant(q, from, to)).collect()),
    }
}

fn rename_name_v(n: &Name, from: u64, to: u64) -> Name {
    match n {
        Name::Var(k) if *k == from => Name::Var(to),
        Name::Var(k) => Name::Var(*k),
        Name::Quote(p) => Name::Quote(Box::new(rename_for_variant(p, from, to))),
    }
}

// ---------------------------------------------------------------------------
// The differential properties.
// ---------------------------------------------------------------------------
proptest! {
    /// The library and the reference agree on `≡` for every random pair.
    #[test]
    fn agree_on_structural_congruence(a in arb_proc(), b in arb_proc()) {
        prop_assert_eq!(structurally_congruent(&a, &b), reference::equiv(&a, &b));
    }

    /// The library and the reference agree on `≡N` for every random pair of
    /// quoted processes.
    #[test]
    fn agree_on_name_equivalence(a in arb_proc(), b in arb_proc()) {
        let m = quote(a);
        let n = quote(b);
        prop_assert_eq!(lib_name_equiv(&m, &n), reference::name_equiv(&m, &n));
    }

    /// A genuine `≡`-witness: both procedures must judge `p` and its congruent
    /// variant equal (covering the positive direction — no under-approximation).
    #[test]
    fn both_accept_congruent_variants(p in arb_proc()) {
        let v = congruent_variant(&p);
        prop_assert!(structurally_congruent(&p, &v), "library rejected a real congruence");
        prop_assert!(reference::equiv(&p, &v), "reference rejected a real congruence");
    }

    /// A near-miss: changing one leaf should make both judge the terms distinct
    /// (covering the negative direction — no over-approximation), unless the
    /// edit happens to be absorbed by `≡` (in which case they must still agree).
    #[test]
    fn agree_on_near_miss(p in arb_proc()) {
        let perturbed = par([p.clone(), lift(quote(lift(quote(zero()), zero())), zero())]);
        prop_assert_eq!(
            structurally_congruent(&p, &perturbed),
            reference::equiv(&p, &perturbed),
        );
    }
}
