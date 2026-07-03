//! On-the-fly (lazy) model checking for the reachability / safety fragment
//! (issue #11): early-exit exploration that agrees with the full-LTS checker but
//! stops at the first counterexample / witness, without building the whole state
//! space.
//!
//! Three groups of tests:
//!
//! * **basic** — the API on small, fully-explorable systems (witness / no
//!   witness, counterexample / holds, zero-length runs, exactness).
//! * **differential** — over many seeded-random ρ-systems, the on-the-fly
//!   verdict and run must AGREE with `Lts::explore` + `check`/`witness`/
//!   `counterexample`, and every returned run must be a genuine path in the LTS.
//! * **acceptance** — a system with a SHALLOW violation but a LARGE reachable
//!   space: on-the-fly finds it while exploring far fewer states than the full
//!   exploration would (and under a bound too small for full exploration).

use stratum_core::term::{drop_, input, lift, output, par, quote, zero};
use stratum_core::{name_equiv, Name, Proc};
use stratum_logic::examples::emits;
use stratum_logic::{
    ag, check_safety, counterexample, ef, find_reachable, holds, neg, prop, witness, Run,
};
use stratum_lts::Lts;

// ===========================================================================
// Shared channels and predicates.
// ===========================================================================

/// The observable `goal` channel `@(@0!(0))`.
fn goal() -> Name {
    quote(lift(quote(zero()), zero()))
}

/// A second observable `bad` channel `@(@0!(@0!(0)))`, distinct from `goal`.
fn bad() -> Name {
    quote(lift(quote(zero()), lift(quote(zero()), zero())))
}

/// Whether a run is a genuine path of `lts`: it starts at the initial state and
/// every step follows a real transition (matching firing channel) to the
/// recorded target state. This validates that an on-the-fly run is a real
/// reduction sequence, using the fully-built LTS as an independent oracle.
fn run_is_genuine_path(lts: &Lts, run: &Run) -> bool {
    let Some(mut cur) = lts.state_index(&run.start) else {
        return false;
    };
    if cur != lts.initial() {
        return false;
    }
    for step in &run.steps {
        let Some(target) = lts.state_index(&step.state) else {
            return false;
        };
        let ok = lts
            .transitions(cur)
            .iter()
            .any(|t| name_equiv(&t.label, &step.channel) && t.target == target);
        if !ok {
            return false;
        }
        cur = target;
    }
    true
}

// ===========================================================================
// Basic API tests.
// ===========================================================================

/// `a⟨|0|⟩ | a(y).goal⟨|0|⟩` — one Comm reaches a goal-emitting state.
fn emitting_system() -> Proc {
    let a = quote(zero());
    par([
        lift(a.clone(), zero()),
        input(a, move |_| lift(goal(), zero())),
    ])
}

#[test]
fn reachability_finds_shallow_witness() {
    let sys = emitting_system();
    let r = find_reachable(&sys, 100, |p: &Proc| emits(p, &goal()));
    assert!(r.reached(), "goal is reachable");
    let w = r.witness.unwrap();
    assert_eq!(w.len(), 1, "one Comm reaches the goal state");
    assert!(
        emits(w.last_state(), &goal()),
        "the run ends at a goal state"
    );
    assert!(r.exact, "fully explored: definitive");
}

#[test]
fn reachability_none_when_unreachable() {
    // `a⟨|0|⟩ | a(_).0` — never emits goal.
    let a = quote(zero());
    let sys = par([lift(a.clone(), zero()), input(a, |_| zero())]);
    let r = find_reachable(&sys, 100, |p: &Proc| emits(p, &goal()));
    assert!(!r.reached());
    assert!(r.exact, "fully explored negative verdict is definitive");
}

#[test]
fn reachability_zero_length_when_start_qualifies() {
    // The start state already emits goal.
    let sys = lift(goal(), zero());
    let r = find_reachable(&sys, 100, |p: &Proc| emits(p, &goal()));
    let w = r.witness.expect("start already qualifies");
    assert!(w.is_empty(), "zero-length witness");
    assert_eq!(r.explored, 1);
}

#[test]
fn safety_finds_shallow_counterexample() {
    let sys = emitting_system();
    // Invariant: "never emits goal".
    let s = check_safety(&sys, 100, |p: &Proc| !emits(p, &goal()));
    assert!(!s.holds(), "the invariant is violated");
    let cex = s.counterexample.unwrap();
    assert_eq!(cex.len(), 1);
    assert!(
        emits(cex.last_state(), &goal()),
        "ends at a violating state"
    );
    assert!(s.exact);
}

#[test]
fn safety_holds_when_invariant_never_violated() {
    // `a⟨|0|⟩ | a(_).0` — goal is never emitted, so "never goal" holds.
    let a = quote(zero());
    let sys = par([lift(a.clone(), zero()), input(a, |_| zero())]);
    let s = check_safety(&sys, 100, |p: &Proc| !emits(p, &goal()));
    assert!(s.holds());
    assert!(s.exact, "fully explored: definitive holds");
}

// ===========================================================================
// Differential test: agreement with the full-LTS checker over random systems.
// ===========================================================================

/// A tiny deterministic xorshift64* PRNG (no deps, no wall-clock). Seeded from a
/// loop index so the whole differential sweep is reproducible.
struct XorShift(u64);

impl XorShift {
    fn new(seed: u64) -> Self {
        // Avoid the fixed point at 0.
        XorShift(seed ^ 0x9E37_79B9_7F4A_7C15)
    }
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
}

/// Three distinct working channels `a`, `b`, `c` (all `≢N` `goal`/`bad`).
fn ch_a() -> Name {
    quote(zero()) // @0
}
fn ch_b() -> Name {
    quote(input(quote(zero()), |_| zero())) // @(@0(_).0)
}
fn ch_c() -> Name {
    quote(lift(quote(zero()), drop_(quote(zero())))) // @(@0!(*@0))
}

/// A replicator on `c` that, on each firing, re-sends and runs its payload —
/// generating unboundedly many distinct states (the divergence engine).
fn replicator(c: Name) -> Proc {
    input(c.clone(), move |y| {
        par([output(c.clone(), y.clone()), drop_(y)])
    })
}

/// Build one random closed ρ-system as a parallel composition of 2..=5 gadgets
/// drawn from a fixed pool. The pool mixes senders, receivers that emit `goal`
/// or `bad` or forward, deadlocking receivers, and a diverging replicator, so
/// reachability of `goal` and safety of "never `bad`" vary independently across
/// seeds.
fn random_system(rng: &mut XorShift) -> Proc {
    let gadget = |k: u64| -> Proc {
        match k {
            0 => lift(ch_a(), zero()),
            1 => lift(ch_b(), zero()),
            2 => input(ch_a(), |_| lift(goal(), zero())), // a -> goal
            3 => input(ch_a(), |_| lift(ch_b(), zero())), // a -> b
            4 => input(ch_b(), |_| lift(goal(), zero())), // b -> goal
            5 => input(ch_b(), |_| lift(bad(), zero())),  // b -> bad
            6 => input(ch_a(), |_| zero()),               // a -> deadlock
            7 => input(ch_b(), |_| zero()),               // b -> deadlock
            8 => {
                // A self-feeding diverger on `c` (unbounded distinct states).
                let seed = lift(ch_c(), par([replicator(ch_c()), lift(ch_a(), zero())]));
                par([seed, replicator(ch_c())])
            }
            _ => lift(bad(), zero()), // immediate bad
        }
    };
    let count = 2 + rng.below(4); // 2..=5 gadgets
    let parts: Vec<Proc> = (0..count).map(|_| gadget(rng.below(10))).collect();
    par(parts)
}

#[test]
fn differential_agreement_with_full_checker() {
    const SEEDS: u64 = 300;
    const BOUND: usize = 80;

    let mut reach_true = 0usize;
    let mut cex_found = 0usize;
    let mut truncated_cases = 0usize;

    for seed in 0..SEEDS {
        let mut rng = XorShift::new(seed);
        let sys = random_system(&mut rng);

        // The full oracle: build the whole bounded LTS and run the denotational
        // checker on the same bound.
        let lts = Lts::explore(&sys, BOUND);
        let label_g = |p: &str, s: &Proc| match p {
            "goal" => emits(s, &goal()),
            "bad" => emits(s, &bad()),
            _ => false,
        };

        // ---- Reachability: `EF goal` -------------------------------------
        let full_reach = holds(&lts, &ef(prop("goal")), &label_g);
        let otf_reach = find_reachable(&sys, BOUND, |p: &Proc| emits(p, &goal()));

        assert_eq!(
            otf_reach.reached(),
            full_reach,
            "reachability verdict must agree (seed {seed})"
        );
        if let Some(w) = &otf_reach.witness {
            assert!(
                run_is_genuine_path(&lts, w),
                "reachability witness must be a genuine LTS path (seed {seed})"
            );
            // BFS in both ⇒ same shortest length.
            let full_w = witness(&lts, &prop("goal"), &label_g).expect("checker agrees");
            assert_eq!(
                w.len(),
                full_w.len(),
                "witness length must match shortest_path (seed {seed})"
            );
            reach_true += 1;
        }

        // ---- Safety: `AG (¬bad)` -----------------------------------------
        let inv = neg(prop("bad")); // "never emits bad"
        let full_safe = holds(&lts, &ag(inv.clone()), &label_g);
        let full_cex = counterexample(&lts, &inv, &label_g);
        let otf_safe = check_safety(&sys, BOUND, |p: &Proc| !emits(p, &bad()));

        assert_eq!(
            otf_safe.counterexample.is_some(),
            full_cex.is_some(),
            "safety counterexample existence must agree (seed {seed})"
        );
        if let Some(cex) = &otf_safe.counterexample {
            assert!(
                run_is_genuine_path(&lts, cex),
                "counterexample must be a genuine LTS path (seed {seed})"
            );
            assert!(
                emits(cex.last_state(), &bad()),
                "counterexample ends at a real violating state (seed {seed})"
            );
            let full_cex = full_cex.as_ref().unwrap();
            assert_eq!(
                cex.len(),
                full_cex.len(),
                "counterexample length must match shortest_path (seed {seed})"
            );
            cex_found += 1;
        }

        // ---- Exactness / truncation boundary -----------------------------
        // Compare definitive verdicts only over a fully-explored space. When the
        // LTS was NOT truncated, "safety holds" is definitive and must match the
        // AG verdict; on-the-fly `exact` must then also be true.
        if !lts.is_truncated() {
            assert_eq!(
                otf_safe.holds(),
                full_safe,
                "over a fully-explored space, safety holds-verdict must match AG (seed {seed})"
            );
            if otf_safe.holds() {
                assert!(
                    otf_safe.exact,
                    "holds over full space is exact (seed {seed})"
                );
            }
            if !otf_reach.reached() {
                assert!(
                    otf_reach.exact,
                    "unreachable over full space is exact (seed {seed})"
                );
            }
        } else {
            truncated_cases += 1;
        }
    }

    // Sanity: the sweep actually exercised both polarities and the truncation
    // boundary (otherwise the agreement assertions would be vacuous).
    assert!(reach_true > 0, "some systems reach goal");
    assert!(cex_found > 0, "some systems violate safety");
    assert!(
        reach_true < SEEDS as usize,
        "some systems do NOT reach goal"
    );
    assert!(truncated_cases > 0, "some systems truncate (diverging)");
}

// ===========================================================================
// Acceptance benchmark: shallow violation, large/unbounded state space.
// ===========================================================================

/// A scalable system whose reachable space is UNBOUNDED (a replicator on `c`
/// spawns unboundedly many distinct states) yet a safety violation is SHALLOW:
/// `a⟨|0|⟩ | a(_).bad⟨|0|⟩` emits `bad` after a single Comm. The on-the-fly
/// checker should find the violation while exploring a handful of states,
/// whereas `Lts::explore` must enumerate the whole (bounded) space.
fn shallow_bad_deep_space() -> Proc {
    let a = quote(zero());
    let short = par([
        lift(a.clone(), zero()),
        input(a, move |_| lift(bad(), zero())),
    ]);
    // Diverging component on `c`: c⟨|R | a!(0)|> | R, R = c(y).(c[y] | *y).
    let diverger = {
        let seed = lift(ch_c(), par([replicator(ch_c()), lift(ch_a(), zero())]));
        par([seed, replicator(ch_c())])
    };
    par([short, diverger])
}

#[test]
fn acceptance_early_exit_beats_full_construction() {
    let sys = shallow_bad_deep_space();

    // Full exploration under a large bound: the diverger fills it up.
    const FULL_BOUND: usize = 500;
    let lts = Lts::explore(&sys, FULL_BOUND);
    let full_states = lts.num_states();
    assert!(
        lts.is_truncated(),
        "the reachable space exceeds the large bound (it is unbounded)"
    );
    assert!(full_states >= 100, "full exploration builds many states");

    // On-the-fly safety with the SAME large bound: finds the shallow violation
    // almost immediately and stops.
    let s = check_safety(&sys, FULL_BOUND, |p: &Proc| !emits(p, &bad()));
    let cex = s.counterexample.expect("bad is reachable in a few steps");
    assert!(emits(cex.last_state(), &bad()));
    assert!(
        run_is_genuine_path(&lts, &cex),
        "the counterexample is a genuine reachable run"
    );

    // The whole point: far fewer states explored than full construction.
    assert!(
        s.explored * 10 < full_states,
        "on-the-fly explored {} states vs full {} — not << ",
        s.explored,
        full_states
    );

    // And it succeeds even under a bound FAR too small for full exploration to
    // characterize the space (the LTS would be badly truncated), demonstrating
    // "without full state-space construction".
    let tiny = check_safety(&sys, 8, |p: &Proc| !emits(p, &bad()));
    assert!(
        tiny.counterexample.is_some(),
        "on-the-fly finds the shallow counterexample under a tiny bound"
    );
    assert!(
        tiny.explored <= 8,
        "under the tiny bound at most 8 states are ever created"
    );

    // Reachability phrasing of the same shallow goal, for symmetry.
    let r = find_reachable(&sys, FULL_BOUND, |p: &Proc| emits(p, &bad()));
    assert!(r.reached());
    assert!(
        r.explored * 10 < full_states,
        "reachability also early-exits: {} vs {}",
        r.explored,
        full_states
    );
}
