# Stratum — specification decisions

This document records the modelling decisions where the source theory is
informal or admits choices, so that "faithful to the source" is a checkable
contract rather than a matter of taste. Sections are added as grains are built.

The process grain follows Meredith & Radestock, *A Reflective Higher-order
Calculus* (ENTCS 141(5), 2005); the field grain follows the PI-SIGFPT
informational-fields substrate (Witsenhausen intrinsic model / σ-algebras).

---

## F. Field grain (σ) — agents, projections, information fields

The field grain answers "what does an agent know?" as a σ-algebra over a
configuration space. On the bounded LTS the space is finite, and a finite
σ-algebra is exactly a **partition**; its blocks are the field's **atoms** (its
resolution limit).

**F1. Configuration space `H`.** `H` = the reachable states of the trace LTS
(`stratum_lts::Lts`). A state is a canonical process — "the trace flattened".
As with every other grain, `H` is the *bounded* reachable fragment; truncation is
reported by the LTS and inherited here.

**F2. Aspects = channels.** The world is a product `H ⊆ ∏_c content(c)` indexed by
channels `c`. ρ-calculus processes are anonymous and names are global, so the
stable coordinate structure is *per channel*, not per sub-term.

**F3. Coordinate content = presence or payload.** `content(c)` defaults to
**presence**: whether the state has a top-level output (barb) on a channel `≡N c`.
This coincides exactly with the §4 barb semantics, so the field grain composes
with `stratum-equiv`. *Done:* the API is parameterized (`content::observational_field_by`)
so `content(c)` may instead be the **payload multiset** — the canonical lifted
processes pending on `c`, via `content::project_payload` / `content::payload_field`
— for finer fields, without changing the agent model. Presence is exactly
"payload multiset non-empty", so the payload field always refines the presence
field (§F7). The presence API (`project`, `observational_field`) is unchanged.

**F4. Observation = outputs only.** Only outputs are observable (inputs have no
barb; the calculus is asynchronous). An agent never observes another's inputs.

**F5. Agent = (obs, ctl).** An agent is a pair of channel sets: `obs` (channels
it can watch) and `ctl` (channels it can drive). Its *information field* is
determined by `obs`; `ctl` is its space of actions. This is the observe/control
split behind the nature-vs-agents cut.

**F6. Projection and field.** The projection `π_A` restricts a configuration to
`A`'s observed coordinates: `project(state, obs)`. `A`'s field is the pullback
σ-algebra `σ(π_A)` — the partition of `H` where two states are in the same atom
iff their projections agree:

> `field_of(A) = partition of H by (project(s, obs_A) == project(t, obs_A))`.

**F7. Refinement is functorial in `obs`.** `obs_A ⊆ obs_B ⟹ field(obs_B)` refines
`field(obs_A)` (more coordinates ⇒ finer field). The knowledge lattice: `pooled`
= common refinement (agents combine knowledge, finer); `common_knowledge` =
transitive closure of the union (coarser).

**F8. Measurability = legible action.** An action is a map `state → value`. It is
**measurable** w.r.t. field `F` iff it is constant on every atom of `F`,
equivalently iff `F` refines the action's own generated field. This is the
honesty constraint welding knowledge to permitted action, and the formal content
of the self-knowledge theorem: an admissible policy factors through `π_A`.

**F9. Signalling surface.** `ctl_A ∩ obs_B` is where `A`'s actions become `B`'s
observations ("action doubles as signal"); `A`'s controlled coordinates are part
of `B`'s nature.

**F10. No probability.** The field object models *distinctions* only. Following
the source, we are deliberately silent on measure/probability; that is a later,
separate layer.

**F11. Time = filtration.** *Done* (module `filtration`). The sample space `Ω` is
the set of finite runs (traces) of the trace LTS; `filtration::enumerate_traces`
enumerates the maximal runs (each extended until a terminal state or `max_len`
steps). Along a run, an agent's field is a non-decreasing sequence of refinements
`F_0 ⊆ F_1 ⊆ … ⊆ F_T` over `Ω` (memory = refusal to coarsen): `F_t` partitions
two runs into the same atom iff the agent's observation sequence — its presence
projection (§F3) of each visited state — agrees on the first `t` visited states.
`F_0` is trivial (no observations yet). `filtration::filtration` builds the
sequence and `filtration::is_filtration` checks that each `F_{t+1}` refines `F_t`.
Consistent with §F10, this carries distinctions only, no probability measure.

---

## S. Surface syntax (S) — the concrete DSL

The surface syntax gives an ASCII, human-writable notation for the closed terms
of §2, so terms need not be built by hand with the `stratum-core` constructors.
It lives in `stratum-syntax`. The design decision recorded here is *how the
informal paper notation is transliterated to ASCII, disambiguated with a
precedence, and mapped onto the core AST* — and the **dual-parser** strategy.

**S1. Concrete grammar.** The ASCII transliteration of Meredith's §2.0.1
notation:

```text
P, Q ::= 0 | nil        null process (§2.0.6)
       | x(y) . P        input; binds the name y in P
       | x!(P)           lift / asynchronous output of the process P on x
       | *x              drop / dereference
       | P | Q           parallel
       | ( P )           grouping
x, y  ::= @P             quote ⌜P⌝ — the only name former (§2.0.2)
       | <identifier>    a name bound by an enclosing input
```

`0` and `nil` both denote `Proc::Zero`; `@` is `⌜·⌝`; `!` is lift; `*` is drop.
There is no bracket sugar for output (`x[y]`, §2.0.5); write it explicitly as
`x!(*y)`.

**S2. Precedence and associativity.** `|` is the lowest precedence and
left-associative (flat up to `≡`, §2.3). The input prefix `x(y).` and lift
`x!(…)` bind tighter than `|`, so an input's continuation extends only to the
next `|`: `x(y).*y | Q` is `(x(y).*y) | Q`. `*` binds to a name. `@` binds to a
*primary* process — `0`, `*x`, or a parenthesized group — so `@0!(0)` parses as
`(@0)!(0)` (the quote is of `0`); quoting a compound process requires
parentheses, e.g. `@(@0!(0))`. Lexically: `// …` line comments, insignificant
whitespace, and the two reserved words `0` / `nil`.

**S3. Closed terms / input-bound identifiers.** The pure calculus has no atomic
names — the only names are quotes (§2.0.2) — so its terms are **closed**
(`Proc::is_closed`). The syntax enforces this: an identifier is legal only where
an enclosing input `x(y).…` binds it, and a free (unbound) identifier is a
parse error. Each binder allocates a fresh symbol via `fresh_sym` (§2.0.1 note),
every occurrence of that identifier resolves to the same `Name::Var`, scoping is
lexical, and an inner binder shadows an outer one of the same name. This resolution
descends through quotes, matching the scoping used by `free_vars`/`congruence`,
so a variable that refers to an enclosing input from *inside* a quote is still
bound. Consequently a parsed term always satisfies `is_closed`.

**S4. Dual-parser strategy.** The syntax is realized twice from a single
language definition:

* A **tree-sitter grammar** (`tree-sitter/grammar.js`) is the *tooling spec*: it
  yields a concrete syntax tree, editor highlighting (`queries/highlights.scm`),
  and bound-name scoping (`queries/locals.scm`), with a corpus test suite. The
  generated `parser.c` is committed for reproducibility. As a context-free CST
  grammar it is a deliberate **superset** of the runtime language — it accepts an
  empty/comment-only file and open terms (free identifiers) — and its
  `locals.scm` scoping is an editor-only *approximation* of S3 (it does not model
  that an input's channel is resolved in the enclosing scope, before the binder).
* A hand-written **recursive-descent parser** (`src/`) is the *runtime*: pure
  Rust, no C toolchain, producing `stratum_core::Proc` directly, resolving
  binders and enforcing S3. Public API: `parse(&str) -> Result<Proc, ParseError>`
  and `parse_name(&str) -> Result<Name, ParseError>`, with line/column-tagged
  errors.

The tree-sitter Rust binding (`tree_sitter_language`) is behind the off-by-default
`tree-sitter` feature, so the default build and the whole test suite are pure
Rust. On the closed, non-empty terms that both accept, the two parsers are kept in
agreement by a shared example set (the S1 examples appear in both the corpus
tests and the Rust `tests/`), and by a
print-then-parse round-trip property test over randomly generated closed terms
(`parse(to_source(P)) ≡ P`).

**S5. Declaration preamble (`def`, `new`, macros) — pure surface sugar.** A file
is a preamble of zero or more declarations followed by exactly one required
program process. Everything the preamble introduces is **desugared at parse
time**: `parse` still returns a closed `Proc` and nothing below the parser (the
core AST, reduction, canonicalization) is aware that the sugar ever existed. This
is a deliberate design boundary — the preamble buys human-writable encodings
without extending the object calculus.

* **`new n1, …, nk` is name-generation, not ν.** The ρ-calculus has no
  restriction operator and no atomic names; a name is a quoted process (§2.0.2).
  A "fresh name from nil" is therefore modelled as a canonical distinct quote
  built from `0`: with `rep(0) = 0`, `rep(k+1) = @0!(rep(k))`, the `k`-th ground
  name is `ground(k) = @(rep(k))` — `@0`, `@(@0!(0))`, `@(@0!(@0!(0)))`, …. These
  are pairwise `≢N` (§2.4) and contain no drops, so they are never
  quote/drop-reducible. A single global counter, advanced in declaration order
  across every `new` (top-level and macro-local), assigns each name its
  `ground(k)`; the mapping is deterministic per program. This is *not* the
  π-calculus ν: no scope, no restriction, no α-conversion of the minted name —
  only generation of a distinguished closed name.
* **`def NAME { BODY }` — alias.** `BODY` is a name-expression or a
  process-expression; the definition is usable only in the matching position (a
  mismatch is a parse error). Definitions are collected order-independently
  (two-pass) and may reference one another; cyclic references are rejected
  statically (the reference graph must be acyclic), guaranteeing expansion
  terminates.
* **`def NAME(p1, …, pn) { BODY }` — macro (an "encoding").** `NAME(arg1, …,
  argn)` expands by capture-avoiding substitution: each argument (a name- or
  process-fragment carrying its call-site environment) is placed wherever its
  parameter occurs, then the result is expanded. Wrong arity, or a parameter used
  in an incompatible sort, is a parse error.
  * **Named arguments (`param <- arg`).** Arguments may be supplied *by name* with
    the `<-` connective, `NAME(p1 <- arg1, …)`, binding each argument to the
    parameter of that name. This is **order-independent**: `f(x <- A, y <- B)`,
    `f(y <- B, x <- A)`, and positional `f(A, B)` desugar to the *same* term. It is
    **pure call-site sugar** — named routing changes only which argument fills
    which parameter hole; the two-sort check on each argument is unchanged
    (whether it arrives positionally or by name it is checked against its
    parameter's inferred sort), and hygiene and expansion are identical. A single
    call is **all-or-nothing** (all positional or all named; mixing is a parse
    error). An unknown parameter name, two arguments for one parameter, or a
    declared parameter left without an argument are parse errors. This is a
    call-site-only extension: it does not touch the calculus or the desugared core
    AST. The tree-sitter CST is a permissive superset here too — it accepts mixed
    and unknown-named calls, leaving those rejections to the runtime.
* **Identifier resolution** is lexical, innermost-first: input binder → macro
  parameter → `new` name → `def` alias → macro application → else unbound-error.
  A `def` body resolves under the global environment (top-level `new`s + its
  parameters + its own local `new`s), never the caller's lexical scope, which is
  what makes expansion hygienic.
* **Hygiene.** A macro's local `new x` mints a *fresh* `ground(k)` on every
  expansion (the shared global counter advances), so distinct expansions of the
  same macro fire on distinct channels; input binders inside macro bodies take
  globally-fresh `fresh_sym` symbols. No capture is possible, and every parsed
  program remains closed (`is_closed`).

**S6. Transparency: `to_source` and `expand`.** `to_source(&Proc) -> String`
renders a closed core term back to valid raw surface syntax with every quote
explicit and correct parenthesization; it is the renderer promoted from the
round-trip property test and satisfies `parse(to_source(p)) ≡ p`. `expand(src)
-> Result<String, ParseError>` parses sugared source and re-renders the desugared
core term, so it exhibits the fully-expanded raw program (no `def`/`new`/macros);
it satisfies `parse(expand(src)) ≡ parse(src)`. For example, `expand("new req,
ack\nreq!(0) | req(x).ack!(0)")` is `@0!(0) | @0(v0).@(@0!(0))!(0)`.
