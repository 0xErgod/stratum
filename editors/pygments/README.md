# stratum-pygments

A [Pygments](https://pygments.org/) lexer for the **Stratum** reflective
higher-order ρ-calculus surface syntax (`.strat`).

It mirrors the highlight categories of the authoritative tree-sitter queries in
`crates/stratum-syntax/tree-sitter/queries/highlights.scm` (keywords
`def`/`new` — macros are written `def NAME(...)`, there is no `macro` keyword —
the null process `nil`/`0`, the quote `@` / drop `*` /
lift `!` / par `|` / named-arg `<-` operators, macro-call names, comments,
numbers). Being regex-based it cannot reproduce the parser's structural
disambiguations (e.g. input `x(y).P` vs. macro call `f(args)`); see the module
docstring in `stratum_pygments/lexer.py` for the exact approximations.

This is what the kernel advertises as `language_info.pygments_lexer = "stratum"`,
so Jupyter's static exports (`nbconvert` to HTML/LaTeX) colour Stratum cells once
this package is installed. Live in-editor highlighting in JupyterLab 4 is handled
separately by the CodeMirror 6 extension in `../jupyterlab-stratum/`.

## Install

```bash
pip install pygments
pip install -e editors/pygments        # from the repo root
```

After install the lexer is discoverable by name and mimetype:

```bash
pygmentize -l stratum editors/pygments/tests/sample.strat
echo 'new a\na!(@0) | *a' | pygmentize -l strat
```

Aliases: `stratum`, `strat`. Filenames: `*.strat`. Mimetype: `text/x-stratum`.

## Test

```bash
pip install -e "editors/pygments[test]"
pytest editors/pygments/tests
# or, without pytest:
python editors/pygments/tests/test_lexer.py
```

The tests tokenize `tests/sample.strat` and assert keywords / operators /
comments / macro names get sensible token types (never the catch-all `Error`
or all-`Text` a missing lexer would produce).

> CI does **not** build or test this package — it is a separate, optional
> artifact. The commands above are the manual acceptance check.
