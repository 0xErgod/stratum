//! Hand-written lexer for the surface syntax.
//!
//! Turns a source string into a flat [`Vec`] of [`Token`]s, tracking 1-based
//! line and column for diagnostics. Whitespace is insensitive and `//` line
//! comments run to the end of the line. The keywords are `0` / `nil` (the null
//! process) and the declaration words `def` / `new`; everything else alphabetic
//! is an [`Tok::Ident`]. A trailing [`Tok::Eof`] is always appended so the
//! parser can peek past the end without bounds checks.

use crate::ParseError;

/// A lexical token kind.
///
/// The payload-carrying [`Tok::Ident`] holds the identifier text; all other
/// variants are punctuation or the null-process keyword.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Tok {
    /// The null process, written `0` or `nil`.
    Zero,
    /// The `def` declaration keyword.
    Def,
    /// The `new` declaration keyword.
    New,
    /// An identifier: `[A-Za-z_][A-Za-z0-9_]*` (not `nil`/`def`/`new`).
    Ident(String),
    /// `(`
    LParen,
    /// `)`
    RParen,
    /// `{`
    LBrace,
    /// `}`
    RBrace,
    /// `,`
    Comma,
    /// `!` — the lift operator.
    Bang,
    /// `*` — the drop operator.
    Star,
    /// `@` — the quote operator.
    At,
    /// `.` — the input-prefix separator.
    Dot,
    /// `|` — parallel composition.
    Bar,
    /// `<-` — the named-argument connective (`param <- arg` in a macro call).
    Larrow,
    /// End of input.
    Eof,
}

impl Tok {
    /// A short human-readable description used in error messages.
    pub(crate) fn describe(&self) -> String {
        match self {
            Tok::Zero => "`0`".to_string(),
            Tok::Def => "`def`".to_string(),
            Tok::New => "`new`".to_string(),
            Tok::Ident(s) => format!("identifier `{s}`"),
            Tok::LParen => "`(`".to_string(),
            Tok::RParen => "`)`".to_string(),
            Tok::LBrace => "`{`".to_string(),
            Tok::RBrace => "`}`".to_string(),
            Tok::Comma => "`,`".to_string(),
            Tok::Bang => "`!`".to_string(),
            Tok::Star => "`*`".to_string(),
            Tok::At => "`@`".to_string(),
            Tok::Dot => "`.`".to_string(),
            Tok::Bar => "`|`".to_string(),
            Tok::Larrow => "`<-`".to_string(),
            Tok::Eof => "end of input".to_string(),
        }
    }
}

/// A token together with the source position of its first character.
#[derive(Clone, Debug)]
pub(crate) struct Token {
    /// The token kind and payload.
    pub(crate) kind: Tok,
    /// 1-based line of the token's first character.
    pub(crate) line: usize,
    /// 1-based column of the token's first character.
    pub(crate) col: usize,
}

/// A cursor over the source characters that tracks line/column.
struct Scan<'a> {
    chars: &'a [char],
    i: usize,
    line: usize,
    col: usize,
}

impl Scan<'_> {
    fn peek(&self) -> Option<char> {
        self.chars.get(self.i).copied()
    }

    fn peek2(&self) -> Option<char> {
        self.chars.get(self.i + 1).copied()
    }

    /// Consume and return the current character, advancing line/column.
    fn bump(&mut self) -> Option<char> {
        let c = self.chars.get(self.i).copied()?;
        if c == '\n' {
            self.line += 1;
            self.col = 1;
        } else {
            self.col += 1;
        }
        self.i += 1;
        Some(c)
    }
}

fn is_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

fn is_ident_continue(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// Tokenize `src`, or fail with a [`ParseError`] at the offending character.
pub(crate) fn lex(src: &str) -> Result<Vec<Token>, ParseError> {
    let chars: Vec<char> = src.chars().collect();
    let mut s = Scan {
        chars: &chars,
        i: 0,
        line: 1,
        col: 1,
    };
    let mut toks = Vec::new();

    while let Some(c) = s.peek() {
        // Whitespace.
        if c.is_whitespace() {
            s.bump();
            continue;
        }
        // Line comment `// …`.
        if c == '/' && s.peek2() == Some('/') {
            while let Some(c) = s.peek() {
                if c == '\n' {
                    break;
                }
                s.bump();
            }
            continue;
        }

        let (line, col) = (s.line, s.col);
        let kind = match c {
            '(' => {
                s.bump();
                Tok::LParen
            }
            ')' => {
                s.bump();
                Tok::RParen
            }
            '{' => {
                s.bump();
                Tok::LBrace
            }
            '}' => {
                s.bump();
                Tok::RBrace
            }
            ',' => {
                s.bump();
                Tok::Comma
            }
            '!' => {
                s.bump();
                Tok::Bang
            }
            '*' => {
                s.bump();
                Tok::Star
            }
            '@' => {
                s.bump();
                Tok::At
            }
            '.' => {
                s.bump();
                Tok::Dot
            }
            '|' => {
                s.bump();
                Tok::Bar
            }
            '<' if s.peek2() == Some('-') => {
                s.bump();
                s.bump();
                Tok::Larrow
            }
            c if c.is_ascii_digit() => {
                let mut lexeme = String::new();
                while let Some(d) = s.peek() {
                    if d.is_ascii_digit() {
                        lexeme.push(d);
                        s.bump();
                    } else {
                        break;
                    }
                }
                if lexeme == "0" {
                    Tok::Zero
                } else {
                    return Err(ParseError {
                        line,
                        column: col,
                        message: format!(
                            "unexpected number `{lexeme}`; the only numeral is `0` (the null process)"
                        ),
                    });
                }
            }
            c if is_ident_start(c) => {
                let mut lexeme = String::new();
                while let Some(d) = s.peek() {
                    if is_ident_continue(d) {
                        lexeme.push(d);
                        s.bump();
                    } else {
                        break;
                    }
                }
                match lexeme.as_str() {
                    "nil" => Tok::Zero,
                    "def" => Tok::Def,
                    "new" => Tok::New,
                    _ => Tok::Ident(lexeme),
                }
            }
            other => {
                return Err(ParseError {
                    line,
                    column: col,
                    message: format!("unexpected character `{other}`"),
                });
            }
        };
        toks.push(Token { kind, line, col });
    }

    toks.push(Token {
        kind: Tok::Eof,
        line: s.line,
        col: s.col,
    });
    Ok(toks)
}
