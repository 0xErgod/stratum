# Stratum

An executable core for the **πρσϕ-Formalism** — the computational movement of
the PI-SIGFPT protocol-theory research arc. Stratum is the tool that makes the
formalism *speakable*: a workbench for modelling protocols, running them to
produce traces, and verifying temporal properties over those traces.

The name is from the working definition of a protocol as *a stratum of codified
behaviour* (Rao et al.).

## Foundation

Stratum's process grain is the **reflective higher-order (ρ) calculus** of
Meredith & Radestock, *A Reflective Higher-order Calculus* (ENTCS 141(5), 2005).
It was chosen because it is a *closed* theory of processes: names are quoted
processes, so the theory of names arises wholly from the theory of processes —
unlike the π-calculus, which is parametric in an external theory of names. That
closure is what makes the whole pipeline self-contained.

> Naming note: in the πρσϕ scheme, **ρ** denotes the *trace* grain. Stratum uses
> Meredith's ρ-*calculus* as the *process* grain (π). The two ρ's are distinct.

## The four grains

The πρσϕ-Formalism sees one object — the **trace** — at four grains. Stratum
grows one crate per grain:

| Grain | Faculty        | Role                        | Crate                    | Status |
|-------|----------------|-----------------------------|--------------------------|--------|
| π     | process theory | *generates* the trace       | `stratum-core`           | M1–M2 ✅ |
| ρ     | trace theory   | what a run *is*             | `stratum-lts`            | M3 ✅  |
| σ     | field theory   | *partitions* the trace      | `stratum-field`          | M6 ✅ (static + filtration + payload) |
| ϕ     | temporal logic | *scores* the trace          | `stratum-logic`          | M4 ✅  |

Behavioral equivalence of two systems lives in `stratum-equiv` (N-barbed
bisimulation, §4) — built on the LTS rather than being one of the four grains.

The σ and ϕ grains compose: `stratum-logic` has epistemic operators `K_A`
(knows) and `P_A` (possible) over an agent's information field, so knowledge and
temporal/branching properties can be checked together.

A surface syntax for writing protocols lives in `stratum-syntax`: an ASCII
transliteration of Meredith's notation with a pure-Rust recursive-descent parser
(the runtime) and a tree-sitter grammar (editor highlighting / CST / AST).

## Milestone roadmap

1. **Core (`stratum-core`) — done.** Terms, quote depth, free-vars/closedness,
   the two substitutions (§2.5 syntactic / §2.7 semantic), and canonicalization
   deciding structural congruence `≡` (§2.3) and name equivalence `≡N` (§2.4).
2. **Reduction — done.** The `Comm` rule (§2.8), the nondeterministic one-step
   relation `step`, and bounded `reachable`. Faithfulness anchored by golden
   tests: the §2.8 sugar step and the §3 replication unfolding.
3. **Trace LTS (`stratum-lts`) — done.** `Lts::explore` builds a bounded,
   labelled transition system over canonical states (edges tagged with the
   `≡N`-canonical firing channel), with truncation reporting and DOT export for
   inspection.
4. **Temporal logic (`stratum-logic`) — done.** A modal μ-calculus model checker
   over the LTS (subsuming LTL/CTL): positive-normal-form formulas, fixpoint
   iteration, CTL-style derived operators (`ef`/`ag`/`af`/`eg`/`ex`), and
   witness / counterexample run extraction.
5. **Equivalences (`stratum-equiv`) — done.** N-barbed bisimulation (§4) —
   weak (`≈N`) and strong — parameterized by an observation set, plus
   may-testing (`may_equivalent`). Bounded exploration reports `Inconclusive`
   on truncation and gives a distinguishing reason otherwise.

## Build & test

```sh
cargo test
```

## License

MIT OR Apache-2.0.
