# Stratum — mechanization (Tier 1, complete)

A machine-checked proof, in Rocq/Coq, that Stratum's canonicalizer is a **sound
and complete decision procedure** for structural congruence.

## What's here

`Rho.v` — the reflective higher-order (rho) calculus core:

- **Syntax** (`Proc`, `Name`) — de Bruijn input binders; names are quotes or
  de-Bruijn refs.
- **`pdepth`/`ndepth`** — quote depth (§2.5), the termination measure for ≡N.
- **`scong` (≡, §2.3)** and **`nequiv` (≡N, §2.4)** — the two relations at the
  heart of `stratum-core`, as mutually-recursive `Inductive`s.
- **`canon`** — the canonicalizer (plain structural recursion; AC-normalization
  factored into `norm_par`, sorted by a `pleb` total-order parameter; name-level
  quote-drop applied up to ≡).
- **Theorems (all proved, `Qed`)** — soundness (`canon_sound`), completeness
  (`canon_complete`), and the headline `canon_decides : canon p = canon q <->
  scong p q`, plus the AC lemmas (`norm_par_comm`/`_assoc`/`_unit`), `canon_cong`,
  `nequiv_complete`, and `canon_idem`.

This mirrors the Rust: `Proc`/`Name` ↔ `stratum-core/src/term.rs`; `scong`/`nequiv`
↔ `structurally_congruent`/`name_equiv`; `canon` ↔ `canonicalize`
(`stratum-core/src/congruence.rs`). The Coq model and the Rust engine represent
the **same quotient** (see the modelling-decision block at the top of `Rho.v`,
and `../SPEC.md`).

## Status — Tiers 1–3

**Fully proved on the Rocq Prover 9.0.1** (standard library only). Every
obligation is `Qed`; there is no `Admitted`/`admit` in the development.
Independently verified: `rocq compile` (clean), `Print Assumptions` on every
theorem, and `coqchk` kernel re-verification.

**Tier 3 closed the last axioms.** `pleb` was an abstract `Parameter` with three
assumed order laws; it is now a **concrete** structural comparator
(`proc_compare`), and `pleb_total`/`pleb_antisym`/`pleb_trans` are **proved**
(`Qed`) of it. Consequently `Print Assumptions` on `canon_decides`,
`step_sound`, `step_complete`, and the Tier-3 `reach_sound` all report **`Closed
under the global context` — ZERO axioms** (no `pleb` symbol, no order
assumptions, no type-in-type, no unsafe fixpoints, no assumed positivity).
Making `pleb` concrete also makes `canon`/`step` **executable in the Coq
kernel**, which is what lets them serve as the extracted/`vm_compute`d oracle.

The AC crux was discharged with a standard insertion-sort development
(`insert_perm` → `sort_perm` → `sort_sorted` → `sorted_perm_unique` →
`sort_par_perm`); completeness via `norm_par_cong` (a permutation of components is
`≡`) and mutual induction (`canon_cong`), then `p ≡ canon p = canon q ≡ q`.

## How to check

```sh
# from this directory, with coqc on PATH:
coqc Rho.v
coqchk -o Rho        # independent kernel re-verification + axiom summary
```

`_CoqProject` (`-Q . Stratum`) lets the VsRocq / VS Code extension load the
project.

## Two honest caveats (surfaced by the alignment check)

- **The α / de-Bruijn conversion is out of scope.** The model treats `var n` as an
  opaque atom; it does **not** model the Rust nominal→de-Bruijn conversion
  (`term.rs`/`congruence.rs`: the `env` push/pop, resolving a channel in the outer
  scope before the binder, shadowing, the free-var fallback, descent-through-quotes).
  A bug in Rust's `env` handling would not be caught here — that is covered by the
  round-trip property test (SPEC S4) or a future model.
- **`pleb` is now concrete, but its order is still a design freedom.** As of
  Tier 3 `pleb` is a concrete comparator with the three order laws *proved*, so
  the metatheory is axiom-free. The *relation* `canon p = canon q` remains
  invariant under the choice of order (it means the component multisets are
  permutations — exactly `sort_par_perm`), so `≡` agrees with Rust regardless.
  The chosen `proc_compare` is **not** guaranteed byte-identical to Rust's derived
  `Ord`; the differential harness therefore compares canonical forms **modulo the
  order of parallel components** (it re-sorts `Par` children by Rust `Ord` on both
  sides). If any code ever depends on the specific canonical *representative*
  (hashing/serializing canonical forms, or LTS state identity, SPEC §F1),
  `proc_compare` must be aligned to Rust's `Ord` — still an open obligation, but
  no longer an *axiom*.

## Tier 3 — verified oracle + differential loop (`Extract.v`)

Issue #16. Two deliverables, both resting on the axiom-free `canon`/`step`:

1. **The verified oracle.** `Extract.v` `Extraction`s the proven `canon`,
   `canon_name`, `step` (and `Proc`/`Name`/`pleb`) to OCaml — the committed
   `oracle.ml`/`oracle.mli`. Because this host's OCaml toolchain could not be run
   (the Rocq-platform `ocamlfind` points at a missing prefix; no `ocamlc`/
   `ocamlopt`), the differential **corpus** is instead produced by the Coq
   **kernel**: `vm_compute` of the *same* verified functions on a fixed list of
   closed, de-Bruijn-explicit ρ-terms, serialized to a stable S-expression text
   format. Kernel evaluation of a `Qed`-verified function is the proven oracle
   just as the extracted OCaml would be; only the evaluator differs.

2. **A verified checker slice.** `reach n p` — bounded reachability by unfolding
   `step` — with `reach_sound : In q (reach n p) -> star p q` (`star` = the
   reflexive–transitive closure of `red`). Every state the checker reports is a
   genuine `-->*` reduct; `Print Assumptions reach_sound` is `Closed` (zero
   axioms), resting only on `step_sound`. A companion `is_nf` normal-form test is
   provided with an *honest* soundness statement (`is_nf p = true -> step p = []`)
   — it checks only `p`'s own components, exactly like the Rust `is_normal_form`,
   and does **not** claim `red`-normality.

**Trust chain of the differential** (`crates/stratum-core/tests/oracle_differential.rs`):

```
Rust engine  ⇐  oracle_corpus.txt  ⇐  vm_compute  ⇐  Coq-proven canon/step
(canonicalize/step)   (33 vectors)     (kernel)       (Print Assumptions: ZERO axioms)
```

The test parses the corpus, reconstructs each term nominally, and asserts Rust
`canonicalize`/`step` agree with the oracle on all 33 vectors (10 with a
non-empty step-set), **modulo Par-component order** (the `pleb` freedom above)
and within the α/de-Bruijn boundary (the corpus terms are closed and
de-Bruijn-explicit, so the comparison is of the *engine*, not the unmodelled
nominal→de-Bruijn conversion — which is nonetheless exercised and pinned for
these closed terms).

### Regenerating the corpus / oracle

```sh
# from proofs/, with rocq on PATH
rocq compile -Q . Stratum Rho.v
rocq compile -Q . Stratum Extract.v         # writes oracle.ml(i) + corpus_raw.out
# strip the Coq print wrapper into the committed corpus:
tr -d '\r' < corpus_raw.out \
  | sed '1 s/^[[:space:]]*= "//' | sed '$ d' | sed '$ s/"[[:space:]]*$//' \
  > ../crates/stratum-core/tests/oracle_corpus.txt
```

`corpus_raw.out` is a git-ignored intermediate; `Extract.v`, `oracle.ml(i)`, and
`oracle_corpus.txt` are committed. `Extract.v` is **not** on the CI path (CI
compiles only `Rho.v`), so it never affects the green `rocq compile Rho.v` gate.

## Deferred (honestly, not faked)

The issue also named a μ-calculus fixpoint checker (Knaster–Tarski) and a
bisimulation algorithm (Paige–Tarjan). These are **deferred**, not stubbed:

- A mechanized least/greatest-fixpoint μ-calculus checker requires a semantic
  domain (a modal transition structure over ρ-states with a valuation), a
  monotone-operator library, and the Knaster–Tarski development — a substantial
  research effort in its own right. Admitting a "verified checker" here would be
  dishonest; none is claimed.
- Paige–Tarjan bisimulation minimization likewise needs a partition-refinement
  development and its correctness proof against a coinductive bisimulation.

The Tier-3 deliverable is the genuinely-achievable core the issue prioritized:
the **extracted/kernel-computed verified oracle**, the closed **differential
loop**, and a **real** verified checker slice (`reach_sound`) — all axiom-free —
with the heavier analysis-layer algorithms explicitly left as future work.
