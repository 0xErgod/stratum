"""Pygments lexer for the Stratum reflective ρ-calculus surface syntax (``.strat``).

The single export is :class:`StratumLexer`, registered under the ``pygments.lexers``
entry point (see ``pyproject.toml``) so that ``pygmentize -l stratum`` and any
Pygments consumer (Jupyter's ``nbconvert`` static HTML export, Sphinx, GitHub-via-
Pygments, …) can colour Stratum cells and ``.strat`` files.
"""

from .lexer import StratumLexer

__all__ = ["StratumLexer"]
__version__ = "0.1.0"
