// A CodeMirror 6 `StreamLanguage` tokenizer for the Stratum reflective
// ρ-calculus surface syntax (`.strat`).
//
// ## Why a StreamLanguage and not a full Lezer grammar
//
// The tree-sitter grammar this mirrors
// (`crates/stratum-syntax/tree-sitter/grammar.js`) is only a *superset* CST and
// still needs a GLR `conflicts` entry to keep the input prefix `x(y).P` and a
// macro call `f(args)` apart — both begin `identifier '('`, and the authoritative
// disambiguation is deferred to the recursive-descent runtime (a `def`-declared
// name is the macro). A Lezer LR(1) grammar cannot resolve that ambiguity without
// re-encoding the same runtime knowledge, and would add a `@lezer/generator`
// codegen step for no highlighting benefit. A line/token `StreamLanguage` colours
// exactly the same *lexical* categories as the shipped Pygments lexer, builds with
// zero extra codegen, and gives live per-keystroke highlighting — the pragmatic
// choice. Its one honest approximation matches Pygments': an identifier directly
// before `(` is coloured as a function (call *or* input channel), and identifiers
// are not scope-resolved. The runtime parser remains authoritative.
//
// ## Highlight-category mapping (mirrors `queries/highlights.scm`)
//
//   tree-sitter capture            surface                CM6 tag (@lezer/highlight)
//   -----------------------------  ---------------------  --------------------------
//   @keyword                       def / new / macro      tags.keyword
//   @constant.builtin (nil)        nil / 0                tags.atom
//   @function / @function.call     def NAME / NAME(...)   tags.function(tags.variableName)
//   @variable(.parameter)          identifiers            tags.variableName
//   @operator                      @ * ! | <-             tags.operator
//   @punctuation.delimiter         . ,                    tags.punctuation
//   @punctuation.bracket           () {}                  tags.paren
//   @comment                       // …                   tags.lineComment
//   (none)                         integer literals       tags.number

import { LanguageSupport, StreamLanguage, StreamParser } from '@codemirror/language';
import { tags as t } from '@lezer/highlight';

/** Per-line tokenizer state: were we just after a `def`/`macro` keyword? */
interface StratumState {
  /** True immediately after a `def`/`macro` keyword, until its name is read. */
  expectName: boolean;
}

const KEYWORDS = new Set(['def', 'new', 'macro']);

const parser: StreamParser<StratumState> = {
  name: 'stratum',

  startState(): StratumState {
    return { expectName: false };
  },

  token(stream, state): string | null {
    if (stream.eatSpace()) {
      return null;
    }

    // Line comment.
    if (stream.match('//')) {
      stream.skipToEnd();
      return 'comment';
    }

    // Named-argument arrow (before the single-char `<`/operator rules).
    if (stream.match('<-')) {
      return 'operator';
    }

    const ch = stream.peek();
    if (ch === undefined) {
      stream.next();
      return null;
    }

    // Quote / drop / lift / par operators.
    if ('@*!|'.indexOf(ch) >= 0) {
      stream.next();
      return 'operator';
    }
    // Sequencing dot and separators.
    if ('.,'.indexOf(ch) >= 0) {
      stream.next();
      return 'punctuation';
    }
    // Grouping / body brackets.
    if ('(){}'.indexOf(ch) >= 0) {
      stream.next();
      return 'bracket';
    }

    // Integer literals — but a bare `0` is the null process.
    if (ch >= '0' && ch <= '9') {
      stream.match(/^[0-9]+/);
      return stream.current() === '0' ? 'atom' : 'number';
    }

    // Identifiers / keywords.
    if (/[A-Za-z_]/.test(ch)) {
      const wasExpectingName = state.expectName;
      state.expectName = false;
      stream.match(/^[A-Za-z_][A-Za-z0-9_]*/);
      const word = stream.current();

      if (KEYWORDS.has(word)) {
        // `def`/`macro` bind a name next; `new`'s names stay ordinary variables.
        state.expectName = word === 'def' || word === 'macro';
        return 'keyword';
      }
      if (word === 'nil') {
        return 'atom';
      }
      // The name bound by a preceding `def`/`macro`.
      if (wasExpectingName) {
        return 'function';
      }
      // A macro call (or input channel): identifier directly before `(`.
      if (stream.peek() === '(') {
        return 'function';
      }
      return 'variable';
    }

    // Anything else: consume one char, unstyled.
    stream.next();
    return null;
  },

  languageData: {
    commentTokens: { line: '//' }
  },

  // Map the token-name strings above to concrete CM6 highlight tags.
  tokenTable: {
    keyword: t.keyword,
    atom: t.atom,
    function: t.function(t.variableName),
    variable: t.variableName,
    operator: t.operator,
    punctuation: t.punctuation,
    bracket: t.paren,
    comment: t.lineComment,
    number: t.number
  }
};

/** The Stratum CodeMirror 6 stream language (token stream + highlight tags). */
export const stratumStreamLanguage = StreamLanguage.define<StratumState>(parser);

/** A ready-to-register {@link LanguageSupport} for `.strat` / `text/x-stratum`. */
export function stratum(): LanguageSupport {
  return new LanguageSupport(stratumStreamLanguage);
}
