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

## Status — Tier 1 complete

**Fully proved on the Rocq Prover 9.0.1** (standard library only). All seven
obligations are `Qed`; there is no `Admitted`/`admit` in the development.
Independently verified: `coqc` (clean), `Print Assumptions` on every theorem, and
`coqchk -o` kernel re-verification. The entire metatheory rests on **exactly**
the three `pleb` order laws (`pleb_total`/`pleb_antisym`/`pleb_trans`) plus the
`pleb` symbol — no other axiom, no type-in-type, no unsafe fixpoints, no assumed
positivity.

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
- **`pleb` is an abstract order.** The *relation* `canon p = canon q` is invariant
  under the choice of order (it means the component multisets are permutations —
  exactly `sort_par_perm`), so `≡` agrees with Rust regardless. But if any code
  depends on the specific canonical *representative* (hashing/serializing canonical
  forms, or LTS state identity, SPEC §F1), `pleb` must be instantiated to Rust's
  derived `Ord` — an open obligation.

## Roadmap

- **Tier 2:** a substitution + reduction module — syntactic/semantic substitution
  (§2.5/§2.7), the `Comm` rule (§2.8), and `step` sound & complete w.r.t. `→`.
- **Extraction:** `Extraction` an OCaml reference from the verified definitions to
  serve as a *proven* oracle in `stratum-core`'s differential test harness.
- **Close the `pleb` gap** (optional): instantiate `pleb` with Rust's `Ord` and
  discharge the three order laws, if canonical representatives ever cross the
  Coq/Rust boundary.
