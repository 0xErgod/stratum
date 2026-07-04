"""A :class:`pygments.lexer.RegexLexer` for the Stratum ρ-calculus surface syntax.

The token categories mirror the authoritative tree-sitter highlight queries in
``crates/stratum-syntax/tree-sitter/queries/highlights.scm``:

======================================  ==========================  ==================
Tree-sitter capture                     Surface construct           Pygments token
======================================  ==========================  ==================
``@keyword``                            ``def`` / ``new`` / ``macro``  ``Keyword.Declaration``
``@constant.builtin`` ``(nil)``         ``nil`` / ``0``             ``Keyword.Constant``
``@function`` ``(def name:)``           ``def NAME`` / ``macro NAME``  ``Name.Function``
``@function.call`` ``(call macro:)``    ``NAME(...)``               ``Name.Function``
``@variable.parameter`` (named arg)     ``param <-``                ``Name.Variable``
``@variable``                           bound / free identifiers    ``Name.Variable``
``@operator`` ``@ * ! | <-``            quote/drop/lift/par/arrow   ``Operator``
``@punctuation.delimiter`` ``. ,``      sequencing / separators     ``Punctuation``
``@punctuation.bracket`` ``() {}``      grouping / bodies           ``Punctuation``
``@comment``                            ``// …``                    ``Comment.Single``
(no tree-sitter node)                   integer literals            ``Number.Integer``
======================================  ==========================  ==================

Being regex-based, this lexer cannot reproduce the parser's structural
disambiguations. In particular an input channel ``x(y).P`` and a macro call
``f(args)`` both read as *identifier ``(``* (the GLR conflict documented in the
grammar), so any identifier immediately followed by ``(`` is coloured as a
function name. Likewise identifiers are not scope-resolved: every non-keyword
identifier is ``Name.Variable``. These are the same "editor-only approximation"
caveats the tree-sitter ``locals.scm`` calls out; the recursive-descent runtime
is authoritative.
"""

from pygments.lexer import RegexLexer, bygroups
from pygments.token import (
    Comment,
    Keyword,
    Name,
    Number,
    Operator,
    Punctuation,
    Whitespace,
)

__all__ = ["StratumLexer"]


class StratumLexer(RegexLexer):
    """Lexer for ``.strat`` files (the reflective higher-order ρ-calculus)."""

    name = "Stratum"
    aliases = ["stratum", "strat"]
    filenames = ["*.strat"]
    mimetypes = ["text/x-stratum"]
    url = "https://github.com/0xErgod/stratum"

    tokens = {
        "root": [
            (r"\s+", Whitespace),
            # Line comments.
            (r"//[^\n]*", Comment.Single),
            # `def NAME` / `macro NAME` — a declaration keyword binding a name.
            (
                r"\b(def|macro)\b(\s+)([A-Za-z_][A-Za-z0-9_]*)",
                bygroups(Keyword.Declaration, Whitespace, Name.Function),
            ),
            # `new` — mint fresh names (its names are ordinary identifiers below).
            (r"\bnew\b", Keyword.Declaration),
            # The null process `nil` / `0` (tree-sitter `@constant.builtin`).
            (r"\bnil\b", Keyword.Constant),
            (r"\b0\b", Keyword.Constant),
            # Other integer literals.
            (r"\b\d+\b", Number.Integer),
            # A macro call (or input channel): identifier immediately before `(`.
            (r"[A-Za-z_][A-Za-z0-9_]*(?=\s*\()", Name.Function),
            # A named-argument parameter: identifier immediately before `<-`.
            (r"[A-Za-z_][A-Za-z0-9_]*(?=\s*<-)", Name.Variable),
            # Operators: named-arg arrow first (so `<` is not read alone).
            (r"<-", Operator),
            (r"[@*!|]", Operator),
            # Sequencing dot and separators.
            (r"[.,]", Punctuation),
            # Grouping / body brackets.
            (r"[(){}]", Punctuation),
            # Any remaining identifier: a bound/free name.
            (r"[A-Za-z_][A-Za-z0-9_]*", Name.Variable),
        ],
    }
