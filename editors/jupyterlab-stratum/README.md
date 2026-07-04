# jupyterlab-stratum

A **JupyterLab 4** extension that registers a **CodeMirror 6** language for the
Stratum reflective ρ-calculus surface syntax, so `.strat` files and Stratum
kernel cells (`text/x-stratum`) are **live-highlighted** as you type.

## Design: StreamLanguage, not a Lezer grammar

JupyterLab 4 uses CodeMirror 6 / Lezer. This extension colours tokens with a
CodeMirror 6 [`StreamLanguage`](https://codemirror.net/docs/ref/#language.StreamLanguage)
tokenizer (`src/stratum.ts`) rather than a compiled Lezer grammar.

Rationale: the authoritative tree-sitter grammar
(`../../crates/stratum-syntax/tree-sitter/grammar.js`) is a *superset* CST that
still needs a GLR `conflicts` entry because an input prefix `x(y).P` and a macro
call `f(args)` both begin `identifier '('` — the disambiguation is deferred to
the runtime recursive-descent parser (a `def`-declared name is the macro). An
LR(1) Lezer grammar cannot resolve that without re-encoding runtime knowledge and
would add a `@lezer/generator` codegen step for no highlighting gain. A
`StreamLanguage` colours exactly the same lexical categories as the shipped
Pygments lexer, needs zero codegen, and gives live per-keystroke highlighting.
Its one honest approximation (shared with Pygments): an identifier directly
before `(` is coloured as a function — call or input channel — and identifiers
are not scope-resolved.

### Highlight-category mapping (mirrors `queries/highlights.scm`)

| tree-sitter capture         | surface              | CM6 tag (`@lezer/highlight`)      |
| --------------------------- | -------------------- | --------------------------------- |
| `@keyword`                  | `def` `new` `macro`  | `tags.keyword`                    |
| `@constant.builtin` `(nil)` | `nil` / `0`          | `tags.atom`                       |
| `@function[.call]`          | `def NAME` / `f(...)`| `tags.function(tags.variableName)`|
| `@variable[.parameter]`     | identifiers          | `tags.variableName`               |
| `@operator`                 | `@ * ! | <-`         | `tags.operator`                   |
| `@punctuation.delimiter`    | `.` `,`              | `tags.punctuation`                |
| `@punctuation.bracket`      | `()` `{}`            | `tags.paren`                      |
| `@comment`                  | `// …`               | `tags.lineComment`                |
| (none)                      | integer literals     | `tags.number`                     |

## Build

```bash
cd editors/jupyterlab-stratum
jlpm install
jlpm build          # tsc compile of src/ -> lib/ (the automated acceptance)
jlpm check:types    # tsc --noEmit type check
```

`jlpm build` runs only `tsc`, so it needs no running Jupyter. To produce the
loadable lab bundle you additionally need a JupyterLab install:

```bash
jlpm build:labextension   # webpack via @jupyterlab/builder (needs jupyterlab)
```

## Install into JupyterLab (manual, for live highlighting)

```bash
cd editors/jupyterlab-stratum
jlpm install && jlpm build:all
jupyter labextension develop . --overwrite
```

Then start `jupyter lab`. Open a `.strat` file or a cell in a notebook running
the Stratum kernel and the ρ-calculus syntax is highlighted live.

> **Manual verification only.** Seeing the colours requires a running JupyterLab;
> that cannot be asserted headlessly here. The automated acceptance for this
> package is that `jlpm install && jlpm build` (i.e. the `tsc` compile) succeeds
> with no type errors.

## Committed vs. generated

Only source and config are committed (`src/`, `style/`, `package.json`,
`tsconfig.json`, `README.md`). Build outputs (`node_modules/`, `lib/`,
`*.tsbuildinfo`, `.yarn/`, `jupyterlab_stratum/labextension/`) are git-ignored via
`../.gitignore`.
