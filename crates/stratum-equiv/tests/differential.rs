//! Differential test: the partition-refinement decision procedure (the public
//! API) must agree, verdict-for-verdict, with the original cross-product
//! greatest-fixpoint oracle ([`stratum_equiv::naive`]) on many random small
//! ρ-processes, for both the strong and weak relations.
//!
//! Agreement is checked at the *discriminant* level — `is_equivalent()` and the
//! Inconclusive-vs-decided split — not on exact reason strings (the two
//! procedures word their diagnostics differently). Seeds are derived from the
//! loop index (a small self-contained xorshift PRNG), so the run is fully
//! deterministic with no `rand` dependency and no wall-clock.

use stratum_core::term::{input, lift, output, par, quote, zero};
use stratum_core::{Name, Proc};
use stratum_equiv::{naive, strong_barbed_bisimilar, weak_barbed_bisimilar, Verdict};

/// Minimal xorshift64* PRNG — deterministic, dependency-free.
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        // Avoid the zero fixed point.
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

/// The pool of channels used to build/observe processes. `@0` and `@(@0!0)`
/// double as the observation set so barbs actually fire; the extras add
/// distinguishing structure.
fn chan(k: usize) -> Name {
    match k % 4 {
        0 => quote(zero()),                      // @0
        1 => quote(lift(quote(zero()), zero())), // @(@0!0)
        2 => quote(output(quote(zero()), quote(zero()))),
        _ => quote(par([zero(), lift(quote(zero()), zero())])),
    }
}

/// Generate a random closed process of bounded depth from the channel pool.
fn gen(rng: &mut Rng, depth: usize) -> Proc {
    if depth == 0 {
        return zero();
    }
    match rng.below(6) {
        0 => zero(),
        1 => lift(chan(rng.below(4)), gen(rng, depth - 1)),
        2 => {
            let c = chan(rng.below(4));
            input(c, |_| gen_boxed(rng, depth - 1))
        }
        3 => {
            // input whose body may reuse the received name as a channel.
            let c = chan(rng.below(4));
            input(c, |y| {
                if rng_bool(rng) {
                    lift(y, zero())
                } else {
                    zero()
                }
            })
        }
        4 => {
            let k = 1 + rng.below(3);
            par((0..k).map(|_| gen(rng, depth - 1)))
        }
        _ => output(chan(rng.below(4)), chan(rng.below(4))),
    }
}

// `gen` needs a `FnOnce` for the input body; these helpers thread the borrow.
fn gen_boxed(rng: &mut Rng, depth: usize) -> Proc {
    gen(rng, depth)
}
fn rng_bool(rng: &mut Rng) -> bool {
    rng.next_u64() & 1 == 1
}

/// Observation set: the channels that actually appear as barbs.
fn observations() -> [Name; 2] {
    [chan(0), chan(1)]
}

/// Two verdicts agree at the discriminant level: both Inconclusive, or both
/// decided with the same equivalence bit.
fn agree(a: &Verdict, b: &Verdict) -> bool {
    match (a, b) {
        (Verdict::Inconclusive(_), Verdict::Inconclusive(_)) => true,
        (Verdict::Inconclusive(_), _) | (_, Verdict::Inconclusive(_)) => false,
        _ => a.is_equivalent() == b.is_equivalent(),
    }
}

/// Core driver: `count` random pairs, each explored to `bound`, comparing the
/// new procedure against the oracle for both strong and weak. Returns
/// (#equivalent-verdicts-seen, #inconclusive-seen) for coverage reporting.
fn run_batch(count: usize, depth: usize, bound: usize) -> (usize, usize) {
    let obs = observations();
    let mut eq = 0;
    let mut inconclusive = 0;
    for idx in 0..count {
        let mut rng = Rng::new(0xD1CE_0000 ^ idx as u64);
        let p = gen(&mut rng, depth);
        // 25% of the time compare a process to itself (forces Equivalent),
        // otherwise to a freshly generated partner.
        let q = if idx % 4 == 0 {
            p.clone()
        } else {
            gen(&mut rng, depth)
        };

        for weak in [false, true] {
            let (new, oracle) = if weak {
                (
                    weak_barbed_bisimilar(&p, &q, &obs, bound),
                    naive::weak_barbed_bisimilar(&p, &q, &obs, bound),
                )
            } else {
                (
                    strong_barbed_bisimilar(&p, &q, &obs, bound),
                    naive::strong_barbed_bisimilar(&p, &q, &obs, bound),
                )
            };
            assert!(
                agree(&new, &oracle),
                "disagreement (weak={weak}, seed idx={idx}):\n  new    = {new:?}\n  oracle = {oracle:?}\n  P = {p:?}\n  Q = {q:?}"
            );
            if matches!(new, Verdict::Inconclusive(_)) {
                inconclusive += 1;
            } else if new.is_equivalent() {
                eq += 1;
            }
            // Self-comparison must always be Equivalent (reflexivity) unless
            // truncated.
            if idx % 4 == 0 && !matches!(new, Verdict::Inconclusive(_)) {
                assert!(new.is_equivalent(), "reflexivity failed: {new:?} for {p:?}");
            }
        }
    }
    (eq, inconclusive)
}

#[test]
fn differential_random_generous_bound() {
    // Bound large enough that most systems terminate — exercises the "decided"
    // path (Equivalent / Distinguished) heavily: identical processes,
    // distinct-barb processes, and same-barb-different-branching processes.
    let (eq, _inc) = run_batch(2000, 4, 200);
    assert!(eq > 0, "expected some Equivalent verdicts for coverage");
}

#[test]
fn differential_random_tight_bound() {
    // A deliberately tight bound so some deeper/branchier systems truncate —
    // exercises the Inconclusive path and its agreement between the two
    // procedures.
    let (_eq, inc) = run_batch(1500, 5, 6);
    assert!(
        inc > 0,
        "expected some Inconclusive verdicts under a tight bound"
    );
}

#[test]
fn differential_obviously_distinct_barbs() {
    // An emitter vs. a non-emitter is Distinguished under both strong and weak,
    // by both procedures.
    let obs = observations();
    let emit = lift(chan(0), zero());
    let quiet = zero();
    for weak in [false, true] {
        let (new, oracle) = if weak {
            (
                weak_barbed_bisimilar(&emit, &quiet, &obs, 100),
                naive::weak_barbed_bisimilar(&emit, &quiet, &obs, 100),
            )
        } else {
            (
                strong_barbed_bisimilar(&emit, &quiet, &obs, 100),
                naive::strong_barbed_bisimilar(&emit, &quiet, &obs, 100),
            )
        };
        assert!(agree(&new, &oracle));
        assert!(!new.is_equivalent());
    }
}

#[test]
fn differential_weak_neq_strong_oracle() {
    // Pin the strong≠weak discriminant against the *oracle* (not just the public
    // path): `x!0` vs `a!0 | a(y).x!0` barb on `x` either immediately or after
    // one internal τ. They are weakly Equivalent but strongly Distinguished, and
    // the new procedure must agree with `naive` on both — so the oracle itself
    // witnesses that the two modes diverge here.
    let x = chan(0); // @0 — the sole observed channel
    let a = chan(2); // an *unobserved* internal relay channel (not in `obs`)
    let obs = [x.clone()]; // observe only `x`, so the relay on `a` is silent

    let emits_now: Proc = lift(x.clone(), zero());
    let emits_after_tau: Proc = par([
        lift(a.clone(), zero()),
        input(a.clone(), {
            let x = x.clone();
            move |_| lift(x.clone(), zero())
        }),
    ]);

    // Weak: both procedures say Equivalent.
    let new_w = weak_barbed_bisimilar(&emits_now, &emits_after_tau, &obs, 100);
    let ora_w = naive::weak_barbed_bisimilar(&emits_now, &emits_after_tau, &obs, 100);
    assert!(
        agree(&new_w, &ora_w),
        "weak: new={new_w:?} oracle={ora_w:?}"
    );
    assert!(
        new_w.is_equivalent(),
        "weak should be Equivalent: {new_w:?}"
    );

    // Strong: both procedures say Distinguished (the τ is a real difference).
    let new_s = strong_barbed_bisimilar(&emits_now, &emits_after_tau, &obs, 100);
    let ora_s = naive::strong_barbed_bisimilar(&emits_now, &emits_after_tau, &obs, 100);
    assert!(
        agree(&new_s, &ora_s),
        "strong: new={new_s:?} oracle={ora_s:?}"
    );
    assert!(
        !new_s.is_equivalent(),
        "strong should be Distinguished: {new_s:?}"
    );
}
