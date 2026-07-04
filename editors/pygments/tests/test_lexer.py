"""Tokenization tests for :class:`stratum_pygments.lexer.StratumLexer`.

Run with ``pytest`` after ``pip install pygments`` and ``pip install -e .`` (from
``editors/pygments``). The assertions check that keywords, the null process,
operators, comments, macro-call names and named-argument arrows get *sensible*
token types — not the catch-all ``Error``/``Text`` a missing lexer would yield.
"""

from pathlib import Path

from pygments.token import (
    Comment,
    Error,
    Keyword,
    Name,
    Operator,
    Punctuation,
    Text,
    Token,
)

from stratum_pygments.lexer import StratumLexer

SAMPLE = (Path(__file__).parent / "sample.strat").read_text(encoding="utf-8")


def _tokens(src):
    return list(StratumLexer().get_tokens(src))


def test_entry_point_discoverable_by_name():
    """`pygmentize -l stratum` resolves via the registered entry point."""
    from pygments.lexers import get_lexer_by_name

    for alias in ("stratum", "strat"):
        assert isinstance(get_lexer_by_name(alias), StratumLexer)

    from pygments.lexers import get_lexer_for_mimetype

    assert isinstance(get_lexer_for_mimetype("text/x-stratum"), StratumLexer)


def test_no_error_tokens_on_sample():
    """A well-formed sample must not produce a single ``Error`` token."""
    assert not any(tok is Error for tok, _ in _tokens(SAMPLE))


def test_not_all_plain_text():
    """The lexer must actually classify — not dump everything as ``Text``."""
    kinds = {tok for tok, _ in _tokens(SAMPLE)}
    non_trivial = kinds - {Text, Token.Text.Whitespace, Text.Whitespace}
    assert len(non_trivial) >= 5


def test_category_mapping():
    """Spot-check that each highlight category lands on its expected token."""
    toks = [(t, v) for t, v in _tokens(SAMPLE) if v.strip()]

    def has(token_type, value):
        return any(t is token_type and v == value for t, v in toks)

    # Declaration keywords.
    assert has(Keyword.Declaration, "def")
    assert has(Keyword.Declaration, "new")
    assert has(Keyword.Declaration, "macro")
    # Null process.
    assert has(Keyword.Constant, "nil")
    assert has(Keyword.Constant, "0")
    # `def`/`macro` binder names and macro-call names -> function.
    assert has(Name.Function, "relay")  # both the def and the call
    assert has(Name.Function, "echo")
    # Operators: quote, drop, lift, par, named-arg arrow.
    for op in ("@", "*", "!", "|", "<-"):
        assert has(Operator, op), op
    # Named-argument parameter (identifier before `<-`).
    assert has(Name.Variable, "a")
    # Comment.
    assert any(t in Comment for t, _ in toks)
    # Brackets / separators.
    assert has(Punctuation, "(")
    assert has(Punctuation, "{")
    assert has(Punctuation, ",")


if __name__ == "__main__":
    # Allow running as a plain script (no pytest) for a quick smoke test.
    test_entry_point_discoverable_by_name()
    test_no_error_tokens_on_sample()
    test_not_all_plain_text()
    test_category_mapping()
    print("all stratum pygments lexer checks passed")
