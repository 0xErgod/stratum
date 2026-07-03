//! Tests for symmetry reduction (`Lts::explore_symmetric`).
//!
//! Symmetry reduction is an **opt-in, quotiented** explorer that must agree with
//! the full [`Lts::explore`] on the *preserved* property class — the
//! **symmetry-invariant** observations (barbs on non-interchangeable channels, or
//! on the interchangeable set as a whole) and their `EF`/`AG` verdicts — while
//! collapsing states related by a permutation of the interchangeable channels. It
//! deliberately does **not** preserve predicates that name one interchangeable
//! channel asymmetrically, so those are never asserted here.
//!
//! The suite has five parts:
//!   * an **empty-set pin**: with no interchangeable channels the symmetric
//!     explorer must coincide byte-for-byte with the full [`Lts::explore`];
//!   * unit tests pinning a small orbit collapse;
//!   * a **soundness-guard pin**: a *non-independent* declared set (one channel
//!     buried inside another) must trip the guard and fall back to full
//!     exploration, coinciding exactly with [`Lts::explore`] — so no reachable
//!     behaviour is ever dropped by an ill-declared symmetry;
//!   * a seeded **differential** test over many random *symmetric* ρ-systems,
//!     comparing reachable symmetric barbs and `EF`/`AG` verdicts (via the real
//!     `stratum-logic` checker) and asserting `sym ≤ full` on state count;
//!   * an **acceptance benchmark** of N interchangeable agents, where full
//!     exploration is `2^N` states and symmetry reduction is linear (`N + 1`).
//!
//! Note on scope: the differential generator (`random_symmetric_system`) only ever
//! emits *genuine independent* symmetries — it instantiates one motif uniformly
//! per interchangeable channel, over channels (`distinct_chan(1..)`) none of which
//! occurs inside another — so it exercises the *reduced* path but, by
//! construction, cannot produce a non-genuine (dependent) set. The dependent /
//! guard-fallback case is pinned separately by
//! `non_independent_set_falls_back_to_explore`.

use std::collections::BTreeSet;

use stratum_core::term::{input, lift, output, par, zero};
use stratum_core::{canonicalize_name, name_equiv, Name, Proc};
use stratum_logic::examples::emits;
use stratum_logic::{ag, ef, holds, prop};
use stratum_lts::Lts;

/// A distinct closed channel per `k`: `⌜ k nested lifts ⌝`. `distinct_chan(0)`
/// is `⌜0⌝`; higher `k` are pairwise distinct and never `≡N ⌜0⌝`.
fn distinct_chan(k: usize) -> Name {
    let mut p = zero();
    for _ in 0..k {
        p = lift(Name::Quote(Box::new(zero())), p);
    }
    Name::Quote(Box::new(p))
}

fn components(p: &Proc) -> Vec<&Proc> {
    match p {
        Proc::Zero => Vec::new(),
        Proc::Par(ps) => ps.iter().collect(),
        other => vec![other],
    }
}

/// The set of observed barbs reachable anywhere in `lts` (canonical channels).
fn reachable_barbs(lts: &Lts, observed: &[Name]) -> BTreeSet<Name> {
    let mut set = BTreeSet::new();
    for i in 0..lts.num_states() {
        for c in components(lts.state(i)) {
            if let Proc::Lift { chan, .. } = c {
                if observed.iter().any(|n| name_equiv(chan, n)) {
                    set.insert(canonicalize_name(chan));
                }
            }
        }
    }
    set
}

/// The maximum number of concurrent top-level barbs on channel `chan` reachable
/// anywhere in `lts` — a *symmetry-invariant* count (permuting interchangeable
/// channels never changes the multiplicity of a barb on a fixed channel).
fn max_barb_count(lts: &Lts, chan: &Name) -> usize {
    let mut best = 0;
    for i in 0..lts.num_states() {
        let n = components(lts.state(i))
            .into_iter()
            .filter(|c| matches!(c, Proc::Lift { chan: ch, .. } if name_equiv(ch, chan)))
            .count();
        best = best.max(n);
    }
    best
}

// ---------------------------------------------------------------------------
// Empty interchangeable set: must coincide exactly with `Lts::explore`.
// ---------------------------------------------------------------------------

/// Assert two LTSs are identical: same states in the same order and the same
/// outgoing transitions for each. The symmetric explorer with an empty group runs
/// the very same BFS as [`Lts::explore`], so indices line up exactly.
fn assert_same_lts(a: &Lts, b: &Lts) {
    assert_eq!(a.num_states(), b.num_states(), "state count differs");
    assert_eq!(
        a.num_transitions(),
        b.num_transitions(),
        "transition count differs"
    );
    assert_eq!(a.is_truncated(), b.is_truncated(), "truncation differs");
    for i in 0..a.num_states() {
        assert_eq!(a.state(i), b.state(i), "state {i} differs");
        assert_eq!(
            a.transitions(i),
            b.transitions(i),
            "transitions of state {i} differ"
        );
    }
}

#[test]
fn empty_interchangeable_set_coincides_with_explore() {
    // A few structurally different systems, each explored both ways.
    let a = distinct_chan(1);
    let b = distinct_chan(2);
    let done = distinct_chan(3);

    // (1) a simple reacting pair.
    let sys1 = par([lift(a.clone(), zero()), input(a.clone(), |_| zero())]);
    // (2) two independent pairs (a diamond).
    let sys2 = par([
        lift(a.clone(), zero()),
        input(a.clone(), |_| zero()),
        lift(b.clone(), zero()),
        input(b.clone(), |_| zero()),
    ]);
    // (3) a pair whose receiver emits on a third channel.
    let d = done.clone();
    let sys3 = par([
        lift(a.clone(), zero()),
        input(a.clone(), move |_| lift(d.clone(), zero())),
    ]);

    for sys in [sys1, sys2, sys3] {
        let full = Lts::explore(&sys, 200);
        let sym = Lts::explore_symmetric(&sys, 200, &[]);
        assert_same_lts(&full, &sym);
    }
}

// ---------------------------------------------------------------------------
// Unit test: a minimal orbit collapse.
// ---------------------------------------------------------------------------

/// Two interchangeable agents `cᵢ!(0) | cᵢ(_).0`. The full LTS is the 4-state
/// diamond (each pair fires independently); under `Sym({c₀, c₁})` the two
/// one-fired mid states are a single orbit, so the symmetric LTS has 3 states.
#[test]
fn two_agents_collapse_one_mid_state() {
    let c0 = distinct_chan(1);
    let c1 = distinct_chan(2);
    let sys = par([
        lift(c0.clone(), zero()),
        input(c0.clone(), |_| zero()),
        lift(c1.clone(), zero()),
        input(c1.clone(), |_| zero()),
    ]);

    let full = Lts::explore(&sys, 100);
    let sym = Lts::explore_symmetric(&sys, 100, &[c0, c1]);

    assert_eq!(full.num_states(), 4, "diamond: init, two mids, final");
    assert_eq!(sym.num_states(), 3, "the two mid states are one orbit");
    assert!(sym.num_states() < full.num_states());
    assert!(!sym.is_truncated());
}

// ---------------------------------------------------------------------------
// Soundness guard: a non-independent declared set must fall back to `explore`.
// ---------------------------------------------------------------------------

/// A **non-genuine** symmetry: `c0 = ⌜0⌝` occurs (up to `≡N`) *inside*
/// `c1 = ⌜c0⟨|0|⟩⌝`. Permuting `{c0, c1}` by the naive match-wins rule would not
/// permute the buried `c0`, so it is not an automorphism and could silently drop
/// the reachable `done` barb. The guard must detect this and fall back to the
/// full [`Lts::explore`], so `explore_symmetric` coincides with it *exactly* and
/// preserves every reachable observation.
#[test]
fn non_independent_set_falls_back_to_explore() {
    let c0 = distinct_chan(0); // ⌜0⌝
    let c1 = Name::Quote(Box::new(lift(c0.clone(), zero()))); // ⌜c0⟨|0|⟩⌝  (buries c0)
    let done = distinct_chan(5);

    // `c1⟨|0|⟩ | c1(_).done⟨|0|⟩` reduces on c1 to emit `done`; a stray `c0⟨|0|⟩`
    // is the buried-channel bait the naive quotient would mishandle.
    let d = done.clone();
    let sys = par([
        lift(c1.clone(), zero()),
        input(c1.clone(), move |_| lift(d.clone(), zero())),
        lift(c0.clone(), zero()),
    ]);

    let full = Lts::explore(&sys, 200);
    let sym = Lts::explore_symmetric(&sys, 200, &[c0, c1]);

    // Guard tripped ⇒ no quotient ⇒ byte-for-byte the full exploration.
    assert_same_lts(&full, &sym);

    // And the previously-at-risk `done` barb is preserved (reachable in both).
    let d = done.clone();
    let label = move |_n: &str, proc: &Proc| emits(proc, &d);
    assert!(holds(&full, &ef(prop("done")), &label));
    assert!(
        holds(&sym, &ef(prop("done")), &label),
        "guard fallback must keep EF(done) reachable"
    );
    assert_eq!(
        reachable_barbs(&full, std::slice::from_ref(&done)),
        reachable_barbs(&sym, std::slice::from_ref(&done)),
        "guard fallback must preserve reachable done barbs"
    );
}

// ---------------------------------------------------------------------------
// Differential test over random *symmetric* ρ-systems.
// ---------------------------------------------------------------------------

/// A tiny deterministic xorshift64 PRNG (no deps, no wall-clock).
struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self {
        Rng((seed ^ 0x9E37_79B9_7F4A_7C15) | 1)
    }
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// One agent-motif template, parametric in the agent's *own* interchangeable
/// channel `c`. Every template references only `c` and *shared* (non-permuted)
/// channels, so instantiating the same template for every agent and composing in
/// parallel yields a system genuinely invariant under `Sym(inter)`.
enum Motif {
    /// `c!(0)` — output on the agent's own channel.
    LiftSelf,
    /// `c(_).0` — receive on the agent's own channel.
    RecvSelf,
    /// `c(_).d!(0)` — receive on own channel, emit on shared channel `d`.
    RecvSelfEmitShared(usize),
    /// `s(_).c!(0)` — receive on shared channel `s`, emit on own channel.
    RecvSharedEmitSelf(usize),
    /// `s!(0)` — output on a shared channel (identical across agents).
    LiftShared(usize),
    /// `hub⟨|*c|⟩` — **forward the agent's own name** `c` as a payload on a shared
    /// `hub` channel (output sugar, so the received object is `≡N c`). Paired with
    /// a shared `hub(z).z⟨|0|⟩` consumer (see `random_symmetric_system`) this
    /// reifies a permuted channel *out of a message and back into a channel
    /// position* — the reflective-payload path the independence guard protects.
    ForwardSelf(usize),
}

impl Motif {
    fn random(rng: &mut Rng, num_shared: usize) -> Motif {
        match rng.below(6) {
            0 => Motif::LiftSelf,
            1 => Motif::RecvSelf,
            2 => Motif::RecvSelfEmitShared(rng.below(num_shared)),
            3 => Motif::RecvSharedEmitSelf(rng.below(num_shared)),
            4 => Motif::LiftShared(rng.below(num_shared)),
            _ => Motif::ForwardSelf(rng.below(num_shared)),
        }
    }

    fn instantiate(&self, c: &Name, shared: &[Name]) -> Proc {
        match self {
            Motif::LiftSelf => lift(c.clone(), zero()),
            Motif::RecvSelf => input(c.clone(), |_| zero()),
            Motif::RecvSelfEmitShared(d) => {
                let d = shared[*d].clone();
                input(c.clone(), move |_| lift(d, zero()))
            }
            Motif::RecvSharedEmitSelf(s) => {
                let c = c.clone();
                input(shared[*s].clone(), move |_| lift(c, zero()))
            }
            Motif::LiftShared(s) => lift(shared[*s].clone(), zero()),
            // hub⟨|*c|⟩ — send the agent's own name on the shared hub channel.
            Motif::ForwardSelf(hub) => output(shared[*hub].clone(), c.clone()),
        }
    }
}

/// Build a random ρ-system that is genuinely symmetric under `Sym(inter)`: a set
/// of motif templates is drawn once and instantiated identically for every
/// interchangeable channel, then composed in parallel (optionally with a shared
/// standalone output, which is itself symmetric).
fn random_symmetric_system(rng: &mut Rng, inter: &[Name], shared: &[Name]) -> Proc {
    let motifs_per_agent = 1 + rng.below(2); // 1..=2
    let motifs: Vec<Motif> = (0..motifs_per_agent)
        .map(|_| Motif::random(rng, shared.len()))
        .collect();

    let mut comps = Vec::new();
    for c in inter {
        for m in &motifs {
            comps.push(m.instantiate(c, shared));
        }
    }
    // Optionally seed a shared output (symmetric, since it names no cᵢ).
    if rng.below(2) == 0 {
        comps.push(lift(shared[rng.below(shared.len())].clone(), zero()));
    }
    // Optionally add a shared consumer `hub(z).z⟨|0|⟩` that turns whatever name it
    // receives into a channel — the sink for `ForwardSelf`, exercising a permuted
    // interchangeable channel reified from a message back into a channel position.
    // It names no cᵢ, so the composite stays invariant under `Sym(inter)`.
    if rng.below(2) == 0 {
        let hub = shared[rng.below(shared.len())].clone();
        comps.push(input(hub, |z| lift(z, zero())));
    }
    par(comps)
}

/// For every random symmetric system: the full and symmetric explorations must
/// agree on the preserved class — reachable barbs on the *shared* (invariant)
/// channels, "some interchangeable channel carries a barb", and the per-shared
/// `EF`/`AG` verdicts — and the symmetric LTS must never have more states.
#[test]
fn differential_preserves_symmetric_observations() {
    let inter: Vec<Name> = (1..=3).map(distinct_chan).collect(); // c₀,c₁,c₂
    let shared: Vec<Name> = (10..=11).map(distinct_chan).collect(); // s₀,s₁
    let bound = 600;
    let trials = 400;
    let mut compared = 0;
    let mut strictly_reduced = 0;

    for seed in 0..trials {
        let mut rng = Rng::new(seed as u64);
        let sys = random_symmetric_system(&mut rng, &inter, &shared);

        let full = Lts::explore(&sys, bound);
        let sym = Lts::explore_symmetric(&sys, bound, &inter);
        if full.is_truncated() || sym.is_truncated() {
            continue; // cannot compare a truncated fragment
        }
        compared += 1;

        // (iii) symmetry reduction never grows the state space.
        assert!(
            sym.num_states() <= full.num_states(),
            "seed {seed}: sym {} > full {}",
            sym.num_states(),
            full.num_states()
        );
        if sym.num_states() < full.num_states() {
            strictly_reduced += 1;
        }

        // (i) identical reachable barbs on the (symmetry-invariant) shared
        // channels, and identical presence of a barb on the interchangeable set
        // as a whole.
        assert_eq!(
            reachable_barbs(&full, &shared),
            reachable_barbs(&sym, &shared),
            "seed {seed}: reachable shared barbs differ"
        );
        assert_eq!(
            reachable_barbs(&full, &inter).is_empty(),
            reachable_barbs(&sym, &inter).is_empty(),
            "seed {seed}: presence of an interchangeable barb differs"
        );

        // (ii) identical EF / AG verdicts for each shared barb predicate, via the
        // real μ-calculus checker.
        for (i, s) in shared.iter().enumerate() {
            let s = s.clone();
            let label = move |_name: &str, proc: &Proc| emits(proc, &s);
            let name = format!("s{i}");
            assert_eq!(
                holds(&full, &ef(prop(&name)), &label),
                holds(&sym, &ef(prop(&name)), &label),
                "seed {seed}: EF(shared barb {i}) verdict differs"
            );
            assert_eq!(
                holds(&full, &ag(prop(&name)), &label),
                holds(&sym, &ag(prop(&name)), &label),
                "seed {seed}: AG(shared barb {i}) verdict differs"
            );
        }
    }

    assert!(compared > 200, "too few comparable systems: {compared}");
    assert!(
        strictly_reduced > 0,
        "symmetry reduction never reduced any random system — the fuzzer is vacuous"
    );
}

// ---------------------------------------------------------------------------
// Acceptance benchmark: N interchangeable agents, 2^N full vs linear symmetric.
// ---------------------------------------------------------------------------

/// A system of `n` interchangeable agents `cᵢ!(0) | cᵢ(_).done!(0)`, all emitting
/// on a single shared (non-interchangeable) `done` channel when they react. The
/// `cᵢ` are the interchangeable set; `done` is a fixed, symmetry-invariant
/// observation. Returns the system, the interchangeable set, and `done`.
fn agents_bench(n: usize) -> (Proc, Vec<Name>, Name) {
    let done = distinct_chan(n + 1); // distinct from every cᵢ (1..=n)
    let inter: Vec<Name> = (1..=n).map(distinct_chan).collect();
    let mut comps = Vec::new();
    for c in &inter {
        comps.push(lift(c.clone(), zero()));
        let d = done.clone();
        comps.push(input(c.clone(), move |_| lift(d.clone(), zero())));
    }
    (par(comps), inter, done)
}

#[test]
fn acceptance_exponential_to_linear() {
    // `n` interchangeable agents ⇒ the full LTS is `2^n` (every subset of reacted
    // agents) while symmetry reduction keeps only the *count* of reacted agents,
    // `n + 1`. The orbit representative enumerates `n!` permutations per state, so
    // `n` is kept modest; `2^6 = 64` vs `7` is still a ~9× collapse.
    let n = 6;
    let (sys, inter, done) = agents_bench(n);

    let full = Lts::explore(&sys, 1 << 16);
    let sym = Lts::explore_symmetric(&sys, 1 << 16, &inter);

    assert!(!full.is_truncated() && !sym.is_truncated());

    // Full exploration enumerates every subset of reacted agents: 2^n states.
    assert_eq!(full.num_states(), 1 << n, "full is exponential");
    // Symmetry reduction keeps only the count of reacted agents: n + 1 states.
    assert_eq!(sym.num_states(), n + 1, "symmetric is linear");
    assert!(
        sym.num_states() * 5 < full.num_states(),
        "substantial reduction: {} vs {}",
        sym.num_states(),
        full.num_states()
    );

    // Verdict identity on the preserved (symmetry-invariant) class.
    let d = done.clone();
    let present = move |_name: &str, proc: &Proc| emits(proc, &d);

    // "some agent reaches done" is reachable but not invariant, in both LTSs.
    assert!(holds(&full, &ef(prop("done")), &present));
    assert!(holds(&sym, &ef(prop("done")), &present));
    assert!(!holds(&full, &ag(prop("done")), &present));
    assert!(!holds(&sym, &ag(prop("done")), &present));

    // A never-present barb is unreachable in both.
    let ghost = distinct_chan(n + 5); // never emitted anywhere
    let absent = move |_name: &str, proc: &Proc| emits(proc, &ghost);
    assert!(!holds(&full, &ef(prop("done")), &absent));
    assert!(!holds(&sym, &ef(prop("done")), &absent));

    // Barb-count invariant: the maximum number of concurrent `done` barbs
    // reachable is `n` (all agents reacted) in both — identical.
    assert_eq!(max_barb_count(&full, &done), n);
    assert_eq!(max_barb_count(&sym, &done), n);
    assert_eq!(
        max_barb_count(&full, &done),
        max_barb_count(&sym, &done),
        "barb-count invariant differs"
    );

    // The shared observation is reachable in both.
    assert_eq!(
        reachable_barbs(&full, std::slice::from_ref(&done)),
        reachable_barbs(&sym, std::slice::from_ref(&done))
    );
}
