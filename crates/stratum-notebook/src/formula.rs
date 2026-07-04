//! The small FORMULA sub-language used by `%check` / `%witness` /
//! `%counterexample`.
//!
//! ## Grammar
//!
//! ```text
//! formula := or
//! or      := and  ( '|' and )*
//! and     := unary ( '&' unary )*
//! unary   := ('EF' | 'AG' | 'AF' | 'EG' | 'EX' | '!') unary
//!          | atom
//! atom    := '(' formula ')'
//!          | 'emits' '(' NAME ')'
//! NAME    := a DSL identifier resolvable to a channel via the session namespace
//! ```
//!
//! The only atomic proposition is **`emits(<name>)`**: it holds in a state whose
//! process has a top-level *output barb* on the channel named `<name>` (i.e.
//! `stratum::logic::examples::emits` on that canonical channel). We deliberately
//! keep the vocabulary tiny and faithful — atomic props are output barbs, and
//! nothing more is invented.
//!
//! Each `emits(...)` atom is assigned a generated proposition id; the compiled
//! result carries the `(prop id → channel)` map so callers can build the
//! `Fn(&str, &Proc) -> bool` labelling.

use stratum::core::Name;
use stratum::core::Proc;
use stratum::logic::examples::emits;
use stratum::logic::{af, ag, and as f_and, ef, eg, ex, neg, or as f_or, prop, Formula};

/// A malformed-formula error, with a 1-based column for a caret.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FormulaError {
    /// 1-based column of the offending token.
    pub column: usize,
    /// Human-readable description.
    pub message: String,
}

impl std::fmt::Display for FormulaError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "formula error at column {}: {}",
            self.column, self.message
        )
    }
}

/// Maximum formula-parser recursion depth. Past this we bail with a clean
/// [`FormulaError`] rather than overflowing the native stack (a deeply-nested
/// `EF ( EF ( … ) )` would otherwise abort the whole process — uncatchable by
/// `catch_unwind`). Issue #43 tracks a proper depth guard in the toolkit.
const MAX_FORMULA_DEPTH: usize = 256;

/// A compiled formula plus the atomic `emits` propositions it references.
#[derive(Debug, Clone)]
pub struct CompiledFormula {
    /// The modal-μ formula, ready for `stratum::logic::check` / `holds`.
    pub formula: Formula,
    /// `(generated prop id, resolved channel)` for each `emits(...)` atom.
    pub props: Vec<(String, Name)>,
    /// Whether the formula uses the raw next-time modality `EX`. Callers reject
    /// `EX` against reduced (POR/symmetry) LTSs, which do not preserve it.
    pub uses_ex: bool,
}

impl CompiledFormula {
    /// Build the labelling `Fn(&str, &Proc) -> bool` for this formula: a
    /// proposition holds in a state iff the state emits on the resolved channel.
    pub fn labelling(&self) -> impl Fn(&str, &Proc) -> bool + '_ {
        move |name: &str, state: &Proc| {
            self.props
                .iter()
                .find(|(id, _)| id == name)
                .is_some_and(|(_, chan)| emits(state, chan))
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Ef,
    Ag,
    Af,
    Eg,
    Ex,
    Emits,
    Not,
    And,
    Or,
    LParen,
    RParen,
    Ident(String),
}

/// A token with its 1-based start column.
struct Spanned {
    tok: Tok,
    column: usize,
}

fn lex(src: &str) -> Result<Vec<Spanned>, FormulaError> {
    let chars: Vec<char> = src.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        let column = i + 1;
        match c {
            c if c.is_whitespace() => {
                i += 1;
            }
            '!' => {
                out.push(Spanned {
                    tok: Tok::Not,
                    column,
                });
                i += 1;
            }
            '&' => {
                out.push(Spanned {
                    tok: Tok::And,
                    column,
                });
                i += 1;
            }
            '|' => {
                out.push(Spanned {
                    tok: Tok::Or,
                    column,
                });
                i += 1;
            }
            '(' => {
                out.push(Spanned {
                    tok: Tok::LParen,
                    column,
                });
                i += 1;
            }
            ')' => {
                out.push(Spanned {
                    tok: Tok::RParen,
                    column,
                });
                i += 1;
            }
            c if c.is_alphanumeric() || c == '_' => {
                let start = i;
                while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                    i += 1;
                }
                let word: String = chars[start..i].iter().collect();
                let tok = match word.as_str() {
                    "EF" => Tok::Ef,
                    "AG" => Tok::Ag,
                    "AF" => Tok::Af,
                    "EG" => Tok::Eg,
                    "EX" => Tok::Ex,
                    "emits" => Tok::Emits,
                    _ => Tok::Ident(word),
                };
                out.push(Spanned { tok, column });
            }
            other => {
                return Err(FormulaError {
                    column,
                    message: format!("unexpected character `{other}`"),
                });
            }
        }
    }
    Ok(out)
}

struct Parser<'a> {
    toks: Vec<Spanned>,
    pos: usize,
    resolve: &'a dyn Fn(&str) -> Option<Name>,
    props: Vec<(String, Name)>,
    next_id: usize,
    end_column: usize,
    /// Set when an `EX` modality is parsed (see [`CompiledFormula::uses_ex`]).
    uses_ex: bool,
}

impl Parser<'_> {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|s| &s.tok)
    }

    fn column(&self) -> usize {
        self.toks
            .get(self.pos)
            .map_or(self.end_column, |s| s.column)
    }

    fn bump(&mut self) {
        self.pos += 1;
    }

    /// Bail with a clean error once the recursive descent gets pathologically
    /// deep, so a crafted formula cannot overflow the native stack.
    fn check_depth(&self, depth: usize) -> Result<(), FormulaError> {
        if depth > MAX_FORMULA_DEPTH {
            Err(FormulaError {
                column: self.column(),
                message: format!("formula nesting too deep (max {MAX_FORMULA_DEPTH})"),
            })
        } else {
            Ok(())
        }
    }

    fn parse_or(&mut self, depth: usize) -> Result<Formula, FormulaError> {
        self.check_depth(depth)?;
        let mut left = self.parse_and(depth + 1)?;
        while matches!(self.peek(), Some(Tok::Or)) {
            self.bump();
            let right = self.parse_and(depth + 1)?;
            left = f_or(left, right);
        }
        Ok(left)
    }

    fn parse_and(&mut self, depth: usize) -> Result<Formula, FormulaError> {
        self.check_depth(depth)?;
        let mut left = self.parse_unary(depth + 1)?;
        while matches!(self.peek(), Some(Tok::And)) {
            self.bump();
            let right = self.parse_unary(depth + 1)?;
            left = f_and(left, right);
        }
        Ok(left)
    }

    fn parse_unary(&mut self, depth: usize) -> Result<Formula, FormulaError> {
        self.check_depth(depth)?;
        match self.peek() {
            Some(Tok::Not) => {
                self.bump();
                Ok(neg(self.parse_unary(depth + 1)?))
            }
            Some(Tok::Ef) => {
                self.bump();
                Ok(ef(self.parse_unary(depth + 1)?))
            }
            Some(Tok::Ag) => {
                self.bump();
                Ok(ag(self.parse_unary(depth + 1)?))
            }
            Some(Tok::Af) => {
                self.bump();
                Ok(af(self.parse_unary(depth + 1)?))
            }
            Some(Tok::Eg) => {
                self.bump();
                Ok(eg(self.parse_unary(depth + 1)?))
            }
            Some(Tok::Ex) => {
                self.bump();
                self.uses_ex = true;
                Ok(ex(self.parse_unary(depth + 1)?))
            }
            _ => self.parse_atom(depth + 1),
        }
    }

    fn parse_atom(&mut self, depth: usize) -> Result<Formula, FormulaError> {
        self.check_depth(depth)?;
        match self.peek() {
            Some(Tok::LParen) => {
                self.bump();
                let inner = self.parse_or(depth + 1)?;
                match self.peek() {
                    Some(Tok::RParen) => {
                        self.bump();
                        Ok(inner)
                    }
                    _ => Err(FormulaError {
                        column: self.column(),
                        message: "expected `)`".to_string(),
                    }),
                }
            }
            Some(Tok::Emits) => {
                self.bump();
                if !matches!(self.peek(), Some(Tok::LParen)) {
                    return Err(FormulaError {
                        column: self.column(),
                        message: "expected `(` after `emits`".to_string(),
                    });
                }
                self.bump();
                let (name, col) = match self.toks.get(self.pos) {
                    Some(Spanned {
                        tok: Tok::Ident(n),
                        column,
                    }) => (n.clone(), *column),
                    _ => {
                        return Err(FormulaError {
                            column: self.column(),
                            message: "expected a channel name inside `emits(...)`".to_string(),
                        })
                    }
                };
                self.bump();
                if !matches!(self.peek(), Some(Tok::RParen)) {
                    return Err(FormulaError {
                        column: self.column(),
                        message: "expected `)` to close `emits(...)`".to_string(),
                    });
                }
                self.bump();
                let chan = (self.resolve)(&name).ok_or_else(|| FormulaError {
                    column: col,
                    message: format!(
                        "unknown channel `{name}` — not a name defined in this session"
                    ),
                })?;
                let id = format!("__emits_{}", self.next_id);
                self.next_id += 1;
                self.props.push((id.clone(), chan));
                Ok(prop(&id))
            }
            Some(_) => Err(FormulaError {
                column: self.column(),
                message: "expected a formula (`emits(...)`, `(`, or a modality)".to_string(),
            }),
            None => Err(FormulaError {
                column: self.column(),
                message: "unexpected end of formula".to_string(),
            }),
        }
    }
}

/// Parse a formula, resolving each `emits(<name>)` channel via `resolve`.
///
/// `resolve` maps a DSL identifier to its canonical channel [`Name`] (typically
/// the session namespace's name table).
pub fn parse_formula(
    src: &str,
    resolve: &dyn Fn(&str) -> Option<Name>,
) -> Result<CompiledFormula, FormulaError> {
    let toks = lex(src)?;
    let end_column = src.chars().count() + 1;
    if toks.is_empty() {
        return Err(FormulaError {
            column: 1,
            message: "empty formula".to_string(),
        });
    }
    let mut parser = Parser {
        toks,
        pos: 0,
        resolve,
        props: Vec::new(),
        next_id: 0,
        end_column,
        uses_ex: false,
    };
    let formula = parser.parse_or(0)?;
    if parser.pos != parser.toks.len() {
        return Err(FormulaError {
            column: parser.column(),
            message: "trailing tokens after formula".to_string(),
        });
    }
    Ok(CompiledFormula {
        formula,
        props: parser.props,
        uses_ex: parser.uses_ex,
    })
}
