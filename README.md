# Stratum

[![CI](https://github.com/0xErgod/stratum/actions/workflows/ci.yml/badge.svg)](https://github.com/0xErgod/stratum/actions/workflows/ci.yml)
[![License: MIT OR Apache-2.0](https://img.shields.io/badge/license-MIT%20OR%20Apache--2.0-blue.svg)](#license)

A playground for experimenting with the **reflective ρ-calculus** as a language
for protocol design and analysis. Stratum is a workbench for modelling protocols,
running them to produce traces, and checking temporal, epistemic, and equivalence
properties over those traces — with a Coq-verified core and a Jupyter kernel
front end.

The name is from the working definition of a protocol as *a stratum of codified
behaviour* (Rao et al.).

## Foundation

Stratum's process layer is the **reflective higher-order (ρ) calculus** of
Meredith & Radestock, *A Reflective Higher-order Calculus* (ENTCS 141(5), 2005).
It was chosen because it is a *closed* theory of processes: names are quoted
processes, so the theory of names arises wholly from the theory of processes —
unlike the π-calculus, which is parametric in an external theory of names. That
closure is what makes the whole pipeline self-contained.

## Components

Stratum is a pipeline: write a protocol, reduce it to a trace, and check
properties of that trace. Each stage is its own crate:

| Role                                              | Crate                    | Status |
|---------------------------------------------------|--------------------------|--------|
| process calculus that *generates* the trace       | `stratum-core`           | M1–M2 ✅ |
| the labelled transition system a run *is*         | `stratum-lts`            | M3 ✅  |
| information fields that *partition* the trace      | `stratum-field`          | M6 ✅ (static + filtration + payload) |
| temporal / epistemic model checker over the trace | `stratum-logic`          | M4 ✅  |

Behavioral equivalence of two systems lives in `stratum-equiv` (N-barbed
bisimulation, §4), built directly on the LTS.

Fields and temporal logic compose: `stratum-logic` has epistemic operators `K_A`
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

## Quickstart

Stratum runs the whole pipeline — surface syntax → core process → trace LTS →
temporal verdicts — from a single `.strat` source. A one-shot request/acknowledge
handshake (`crates/stratum/examples/handshake.strat`):

```
new req, ack

req!(0) | req(x).ack!(0)
```

`new req, ack` mints two distinct fresh channel names from nil (`req = @0`,
`ack = @(@0!(0))`) — name-generation, not restriction. The client sends a request
on `req`; the server receives it (binding the reply value `x`, unused here) and
answers by emitting on `ack`.

Run the worked example:

```sh
cargo run -p stratum --example handshake
```

It parses the protocol, prints the `expand` raw-core transparency view (named
channels desugared to the quoted-process names the calculus works with), builds
the bounded trace LTS, and model-checks three temporal properties:

```
== protocol ==
@0!(0) | @0(_).@(@0!(0))!(0)

== expanded (raw core) ==
@0!(0) | @0(v0).@(@0!(0))!(0)

== trace LTS ==
2 states, 1 transitions (truncated: false)

  s0: @0(_).@(@0!(0))!(0) | @0!(0)
  s1: @(@0!(0))!(0) [terminal]

== properties ==
  EF acked   (the request can be acknowledged)      : true
  AF acked   (every run eventually acknowledges)    : true
  AG ~acked  (it is never acknowledged) [expect: false] : false

  witness to `acked`: 1 step(s), s0 -> [1]
  counterexample to `AG ~acked`: reaches s1 in 1 step(s)
```

The LTS has two states: the initial parallel composition `s0` and the terminal
state `s1` where the acknowledgement is pending. `EF acked` and `AF acked` both
hold (the handshake can and always does acknowledge), while the safety invariant
`AG ~acked` is false — the checker returns a one-step witness reaching `s1` and a
matching counterexample.

## Build & test

```sh
cargo test
```

## License

MIT OR Apache-2.0.
