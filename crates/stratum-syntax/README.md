# stratum-syntax

A concrete **surface syntax** (a small DSL) for writing terms of the reflective
higher-order (ρ) calculus of Meredith & Radestock, *A Reflective Higher-order
Calculus* (ENTCS 141(5), 2005), plus two parsers for it:

* a hand-written **recursive-descent parser** — the pure-Rust *runtime*
  (default build, no C toolchain);
* a **tree-sitter grammar** — the *tooling spec* (editor highlighting,
  incremental parsing, an inspectable CST).

Both share the same surface grammar. The tree-sitter grammar is intentionally a
permissive *superset*: as a context-free CST grammar it accepts an empty (or
comment-only) file and open terms with free identifiers, leaving semantics to
tools. The recursive-descent runtime additionally enforces two rules the CST
cannot express — a program is a single **non-empty** process, and every
identifier must be **input-bound** (the closed-term rule, below).

## The syntax

An ASCII transliteration of Meredith's notation:

```text
P, Q ::= 0 | nil        the null process
       | x(y) . P        input on channel x, binding the name y in P
       | x!(P)           lift: asynchronous output of the process P on x
       | *x              drop / dereference of a name
       | P | Q           parallel composition
       | ( P )           grouping
x, y  ::= @P             the quote of a process (the only name former)
       | <identifier>    a name bound by an enclosing input
```

### Precedence and lexing

* `|` (parallel) is the **lowest** precedence, left-associative (and flat up to
  structural congruence).
* The input prefix `x(y).` and lift `x!(…)` bind **tighter than `|`**, so an
  input's continuation runs only up to the next `|`:
  `x(y).*y | Q` parses as `(x(y).*y) | Q`.
* `*` binds tightly to a following **name**.
* `@` binds tightly to a following **primary** process — one of `0`, `*x`, or a
  parenthesized group. Hence `@0!(0)` is `(@0)!(0)`: the quote is of `0`, not of
  `0!(0)`. To quote a compound process, parenthesize it: `@(@0!(0))`.
* Line comments `// …` run to end of line; whitespace is insignificant.
* The only keywords are `0` and `nil` (both = the null process). `nil` is
  reserved and cannot be used as an identifier.
* There is no output-sugar `x[y]` (Meredith §2.0.5); write it explicitly as
  `x!(*y)`.

### Closed terms / the input-bound-identifier rule

Terms of the pure calculus are **closed**: the only free names are quotes `@P`.
A bare identifier is therefore legal **only** when some enclosing input binds it;
a free (unbound) identifier is a parse error. Each binder is resolved to a fresh
symbol (`stratum_core::fresh_sym`) at its `x(y).…`, and every occurrence of `y`
in the continuation resolves to that same `Name::Var`. Scoping is lexical and
inner binders shadow outer ones of the same name. This holds inside quotes too:
`@0(y).@(*y)!(0)` is a legal closed term whose quoted sub-process refers to the
enclosing binder.

## Examples

| Source                      | Core term                                             |
|-----------------------------|-------------------------------------------------------|
| `0`                         | `zero()`                                              |
| `@0!(0)`                    | `lift(quote(zero()), zero())`                         |
| `*@0`                       | `drop_(quote(zero()))`                                |
| `@0(y).*y`                  | `input(quote(zero()), \|y\| drop_(y))`                |
| `@0!(0) \| @0(y).*y`        | the two above in parallel                             |
| `@0(y).(*y \| @0!(0))`      | `input(quote(zero()), \|y\| par([drop_(y), lift(quote(zero()), zero())]))` |

## Declarations: `def`, `new`, and macros

A file may open with a preamble of **declarations**, followed by exactly one
required program process. This is **pure surface sugar**: it is expanded at parse
time, so `parse` still returns an ordinary *closed* `stratum_core::Proc` with no
trace of the declarations — nothing below the parser changes.

```text
def NAME { BODY }              // alias for a name OR a process
def NAME(p1, …, pn) { BODY }   // parameterized macro (an "encoding")
new n1, …, nk                  // mint k DISTINCT fresh ground names
```

```text
new req, ack
req!(0) | req(x).ack!(0)
```

desugars to the raw term `@0!(0) | @0(x).@(@0!(0))!(0)`.

* **`new` is name-generation, not ν/restriction.** A name in the ρ-calculus is a
  quoted process; a "fresh name from nil" is a canonical distinct quote built
  from `0`: `ground(0) = @0`, `ground(1) = @(@0!(0))`, `ground(2) =
  @(@0!(@0!(0)))`, … (nested lifts over `0`, quoted). A single global counter,
  advanced in declaration order across every `new` (top-level *and* macro-local),
  assigns each minted name its `ground(k)`. These names are pairwise distinct and
  never quote/drop-reducible. There is **no** scoping/restriction operator added
  to the calculus.
* **`def NAME { BODY }`** is an alias whose `BODY` is a name-expression (e.g.
  `@0`) or a process-expression; a name-alias is usable only in name position and
  a process-alias only in process position (a mismatch is a parse error).
  Definitions may reference each other (order-independent); cyclic references are
  rejected.
* **`def NAME(p1, …, pn) { BODY }`** is a macro: `NAME(arg1, …, argn)` expands by
  capture-avoiding substitution of the arguments for the parameters. Each
  argument may be a name- or process-expression and is placed wherever the
  parameter appears; wrong arity or an incompatible position is a parse error.
  * **Named arguments.** A call may pass arguments **by name** with the `<-`
    connective, `NAME(p1 <- arg1, p2 <- arg2, …)`, binding each argument to the
    parameter of that name. This is **order-independent**: `f(x <- A, y <- B)`,
    `f(y <- B, x <- A)`, and positional `f(A, B)` all produce the **same**
    expansion. It is pure call-site sugar — named routing only decides which
    argument lands in which parameter hole; the argument is then expanded and
    **sort-checked exactly as in the positional case** (a process passed to a
    name-parameter, by name or by position, is the same error). A call is
    **all-or-nothing**: every argument positional or every argument named, never
    mixed. Passing an unknown parameter name, giving one parameter two arguments,
    or omitting a declared parameter is a parse error, as is mixing the two forms.
* **Hygiene.** A macro's local `new` mints a *fresh* ground name on *every*
  expansion, so `f(…) | f(…)` for a macro `f` with a `new x` yields two distinct
  internal channels. Input binders inside macro bodies use globally-fresh
  symbols, so no capture is possible.

### Resolution order

A bare identifier resolves, innermost-first: (1) an enclosing input binder →
`Name::Var`; (2) a macro parameter → the substituted argument; (3) a `new` name
→ its `ground(k)`; (4) a `def` alias → its expanded body; (5) `NAME(args)` → the
macro expansion; otherwise it is an unbound-identifier error.

### `expand` — the transparency tool

```rust
use stratum_syntax::{expand, to_source};
use stratum_core::Proc;

// `to_source(&Proc)` renders a core term back to valid raw surface syntax
// (all quotes explicit), satisfying `parse(to_source(p)) ≡ p`.
// `expand(src)` parses the sugared source and re-renders the desugared term.
let raw = expand("new req, ack\nreq!(0) | req(x).ack!(0)").unwrap();
assert_eq!(raw, "@0!(0) | @0(v0).@(@0!(0))!(0)");
# let _ = to_source(&Proc::Zero);
```

`expand` output contains no `def`/`new`/macros and re-parses to a term
structurally congruent to `parse(src)`.

## Using the recursive-descent parser (runtime)

```rust
use stratum_syntax::{parse, parse_name, ParseError};

let p = parse("@0!(0) | @0(y).*y")?;   // -> stratum_core::Proc
let n = parse_name("@0")?;             // -> stratum_core::Name
# Ok::<(), ParseError>(())
```

`parse` / `parse_name` return `Result<_, ParseError>`; `ParseError` carries a
1-based `line`/`column` and a human-readable `message`, and its `Display` renders
`parse error at line L, column C: message`.

```sh
cargo test -p stratum-syntax          # RD parser + round-trip property test
cargo clippy -p stratum-syntax --all-targets
```

## Using the tree-sitter grammar (tooling)

The grammar lives under `tree-sitter/`:

```
tree-sitter/
  grammar.js              the grammar
  tree-sitter.json        grammar metadata
  queries/highlights.scm  syntax highlighting (incl. `def`/`new` keywords)
  queries/locals.scm      bound-name scoping (definitions/references)
  test/corpus/basic.txt          corpus tests (base syntax)
  test/corpus/declarations.txt   corpus tests (def/new/macros)
  src/parser.c            generated parser (committed for reproducibility)
```

Regenerate and test (requires the `tree-sitter` CLI):

```sh
cd tree-sitter
tree-sitter generate
tree-sitter test
```

### Rust binding (optional, off by default)

The generated C parser is exposed to Rust behind the **off-by-default**
`tree-sitter` feature. The default build is pure Rust and needs no C toolchain;
only this feature compiles `tree-sitter/src/parser.c`.

```sh
cargo test -p stratum-syntax --features tree-sitter
```

```rust
# #[cfg(feature = "tree-sitter")]
# fn demo() {
use tree_sitter::Parser;
let mut parser = Parser::new();
parser.set_language(&stratum_syntax::tree_sitter_language()).unwrap();
let tree = parser.parse("@0!(0)", None).unwrap();
assert_eq!(tree.root_node().kind(), "source_file");
# }
```

## Why two parsers?

The tree-sitter grammar is the **specification and tooling surface** — it gives
editors highlighting, incremental reparsing, and a concrete syntax tree for
inspection. The recursive-descent parser is the **runtime**: it produces the
core AST (`stratum_core::Proc`) directly, resolves binders to fresh symbols,
enforces the closed-term rule, and has no non-Rust dependencies. Keeping both in
one crate makes the surface syntax usable from editors and from the library with
a single source of truth for the language.

## License

MIT OR Apache-2.0.
