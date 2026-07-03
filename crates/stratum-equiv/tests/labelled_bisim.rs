//! Tests for labelled bisimulation and its documented relation to barbed
//! congruence (issue #14).
//!
//! The theory (Meredith & Radestock §4; Lybech 2022) says labelled bisimilarity
//! **coincides** with barbed congruence. We do not mechanize the coincidence; we
//! provide a checker plus *evidence* for the load-bearing direction and its
//! consequences:
//!
//! * **Soundness (labelled ⟹ barbed):** every labelled-bisimilar pair is also
//!   weak-barbed-bisimilar — labelled bisim *certifies* barbed equivalence. Pinned
//!   on hand examples and over a seeded random suite.
//! * **Congruence (closed under contexts):** labelled-bisimilar processes stay
//!   equivalent under parallel composition and input prefixing — the whole point
//!   of a congruence.
//! * **Discrimination (labelled is finer):** processes with identical output
//!   barbs but different *input* behaviour are barbed-equivalent yet
//!   labelled-DISTINGUISHED, and a context turns that into a barbed difference —
//!   showing barbed bisim alone is not a congruence, while labelled bisim is.

use stratum_core::term::{input, lift, output, par, quote, zero};
use stratum_core::{Name, Proc};
use stratum_equiv::{
    strong_labelled_bisimilar, weak_barbed_bisimilar, weak_labelled_bisimilar, Verdict,
};

/// Channel pool, doubling as the barbed observation set so barbs fire.
fn chan(k: usize) -> Name {
    match k % 4 {
        0 => quote(zero()),                      // @0
        1 => quote(lift(quote(zero()), zero())), // @(@0!0)
        2 => quote(output(quote(zero()), quote(zero()))),
        _ => quote(par([zero(), lift(quote(zero()), zero())])),
    }
}

fn observations() -> [Name; 4] {
    [chan(0), chan(1), chan(2), chan(3)]
}

// ---------------------------------------------------------------------------
// Discrimination: labelled bisim is finer than (output-only) barbed bisim.
// ---------------------------------------------------------------------------

#[test]
fn labelled_distinguishes_input_that_barbed_equates() {
    // p = x(y).0 has NO output barb (asynchronous input is unobservable to
    // barbs); q = 0 also has none. So they are barbed-equivalent...
    let obs = observations();
    let p = input(chan(0), |_| zero());
    let q = zero();
    assert!(
        weak_barbed_bisimilar(&p, &q, &obs, 200).is_equivalent(),
        "x(y).0 and 0 should be barbed-equivalent (no output barbs)"
    );

    // ...but labelled bisim sees the input action In(x) that q cannot match.
    assert!(
        matches!(
            strong_labelled_bisimilar(&p, &q, 200),
            Verdict::Distinguished(_)
        ),
        "labelled bisim must distinguish an input capability from none"
    );
    assert!(matches!(
        weak_labelled_bisimilar(&p, &q, 200),
        Verdict::Distinguished(_)
    ));
}

#[test]
fn context_reveals_barbed_is_not_a_congruence() {
    // Continuing the previous example: place both in the context  x!0 | [·].
    // C[p] = x!0 | x(y).0  can τ-reduce to 0 (barb on x lost); C[q] = x!0 keeps
    // the barb forever. So a context turns the barbed-equivalent p, q into
    // barbed-DISTINGUISHED processes — barbed bisim is not preserved by
    // contexts. Labelled bisim already told them apart (previous test), i.e. it
    // is the congruence.
    let obs = observations();
    let x = chan(0);
    let p = input(x.clone(), |_| zero());
    let q = zero();

    let cp = par([lift(x.clone(), zero()), p]);
    let cq = par([lift(x.clone(), zero()), q]);

    assert!(
        matches!(
            weak_barbed_bisimilar(&cp, &cq, &obs, 200),
            Verdict::Distinguished(_)
        ),
        "x!0|x(y).0 vs x!0 must be barbed-distinguished (the barb can be consumed)"
    );
}

// ---------------------------------------------------------------------------
// Soundness: labelled-bisimilar ⟹ weak-barbed-bisimilar (hand examples).
// ---------------------------------------------------------------------------

#[test]
fn labelled_equivalent_implies_barbed_equivalent_examples() {
    let obs = observations();
    // Structurally-congruent but syntactically distinct representatives: par is
    // commutative/associative, inputs are α-convertible. These are labelled
    // bisimilar; assert they are barbed-equivalent too.
    let pairs: Vec<(Proc, Proc)> = vec![
        (
            par([lift(chan(0), zero()), lift(chan(1), zero())]),
            par([lift(chan(1), zero()), lift(chan(0), zero())]),
        ),
        (
            input(chan(0), |_| zero()),
            input(chan(0), |_| zero()), // fresh binder symbol, α-variant
        ),
        (
            par([lift(chan(2), zero()), input(chan(2), |y| lift(y, zero()))]),
            par([input(chan(2), |y| lift(y, zero())), lift(chan(2), zero())]),
        ),
    ];
    for (p, q) in pairs {
        assert!(
            strong_labelled_bisimilar(&p, &q, 300).is_equivalent(),
            "expected strong labelled-bisimilar: {p:?} vs {q:?}"
        );
        assert!(
            weak_barbed_bisimilar(&p, &q, &obs, 300).is_equivalent(),
            "labelled-bisimilar pair must be weak-barbed-bisimilar: {p:?} vs {q:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// Congruence: labelled bisim is preserved by contexts.
// ---------------------------------------------------------------------------

#[test]
fn labelled_bisim_is_preserved_by_contexts() {
    // A non-trivial labelled-bisimilar pair (structurally congruent variants).
    let p = par([lift(chan(1), zero()), input(chan(2), |y| lift(y, zero()))]);
    let q = par([input(chan(2), |y| lift(y, zero())), lift(chan(1), zero())]);
    assert!(strong_labelled_bisimilar(&p, &q, 300).is_equivalent());

    // Parallel context:  p | R ~ q | R.
    let r = lift(chan(0), zero());
    let pr = par([p.clone(), r.clone()]);
    let qr = par([q.clone(), r.clone()]);
    assert!(
        strong_labelled_bisimilar(&pr, &qr, 300).is_equivalent(),
        "parallel context must preserve labelled bisimilarity"
    );
    assert!(weak_labelled_bisimilar(&pr, &qr, 300).is_equivalent());

    // Input-prefix context:  x(z).p ~ x(z).q.
    let xp = input(chan(3), {
        let p = p.clone();
        move |_| p
    });
    let xq = input(chan(3), {
        let q = q.clone();
        move |_| q
    });
    assert!(
        strong_labelled_bisimilar(&xp, &xq, 300).is_equivalent(),
        "input-prefix context must preserve labelled bisimilarity"
    );

    // Output/lift context:  x⟨|p|⟩ ~ x⟨|q|⟩  (the emitted process is the same up
    // to ≡, so the lifts are bisimilar as well).
    let lp = lift(chan(0), p);
    let lq = lift(chan(0), q);
    assert!(
        strong_labelled_bisimilar(&lp, &lq, 300).is_equivalent(),
        "lift context must preserve labelled bisimilarity"
    );
}

// ---------------------------------------------------------------------------
// Differential / consistency over random ρ-systems (seeded, dependency-free).
// labelled-bisimilar ⟹ barbed-bisimilar (never asserted in reverse).
// ---------------------------------------------------------------------------

/// Minimal xorshift64* PRNG — deterministic, dependency-free (as in
/// `differential.rs`).
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed ^ 0x9E37_79B9_7F4A_7C15 | 1)
    }
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next_u64() % n as u64) as usize
    }
}

fn gen(rng: &mut Rng, depth: usize) -> Proc {
    if depth == 0 {
        return zero();
    }
    match rng.below(6) {
        0 => zero(),
        1 => lift(chan(rng.below(4)), gen(rng, depth - 1)),
        2 => input(chan(rng.below(4)), |_| zero()),
        3 => input(chan(rng.below(4)), |y| {
            if rng_bool_static() {
                lift(y, zero())
            } else {
                zero()
            }
        }),
        4 => {
            let k = 1 + rng.below(2);
            par((0..k).map(|_| gen(rng, depth - 1)))
        }
        _ => output(chan(rng.below(4)), chan(rng.below(4))),
    }
}

// The input-body closure cannot borrow `rng`; use a fixed shape instead.
fn rng_bool_static() -> bool {
    true
}

/// Two verdicts are comparable only when both are decided (not Inconclusive).
fn both_decided(a: &Verdict, b: &Verdict) -> bool {
    !matches!(a, Verdict::Inconclusive(_)) && !matches!(b, Verdict::Inconclusive(_))
}

#[test]
fn differential_labelled_implies_barbed() {
    let obs = observations();
    let mut eq_seen = 0usize;
    let count = 1500;
    for idx in 0..count {
        let mut rng = Rng::new(0x5EED_0000 ^ idx as u64);
        let p = gen(&mut rng, 4);
        // 30% self-comparisons to force Equivalent verdicts for coverage.
        let q = if idx % 10 < 3 {
            p.clone()
        } else {
            gen(&mut rng, 4)
        };

        for &weak in &[false, true] {
            let lab = if weak {
                weak_labelled_bisimilar(&p, &q, 250)
            } else {
                strong_labelled_bisimilar(&p, &q, 250)
            };
            let barbed = weak_barbed_bisimilar(&p, &q, &obs, 250);

            if both_decided(&lab, &barbed) && lab.is_equivalent() {
                eq_seen += 1;
                // The soundness direction: labelled ⟹ (weak) barbed. Never the
                // reverse.
                assert!(
                    barbed.is_equivalent(),
                    "labelled-bisimilar but NOT barbed-bisimilar (weak={weak}, idx={idx}):\n  \
                     labelled={lab:?}\n  barbed={barbed:?}\n  P={p:?}\n  Q={q:?}"
                );
            }
        }
    }
    assert!(
        eq_seen > 0,
        "expected some labelled-Equivalent verdicts for coverage"
    );
}
