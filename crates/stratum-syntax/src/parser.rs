//! Hand-written recursive-descent parser: tokens → surface AST ([`crate::ast`]).
//!
//! The parser produces an unresolved surface tree; identifier resolution and the
//! desugaring of `def`/`new`/macros into a pure [`stratum_core::Proc`] happen in
//! [`crate::resolve`]. A file is a preamble of declarations followed by exactly
//! one program process:
//!
//! ```text
//! file      ::= decl* process EOF
//! decl      ::= 'def' ident ( '(' params ')' )? '{' block '}'   -- alias / macro
//!             | 'new' ident ( ',' ident )*                       -- ground-name mint
//! block     ::= ('new' ident (',' ident)*)* process             -- def body
//! process   ::= term ( '|' term )*                 -- '|' is lowest precedence
//! term      ::= '0' | 'nil'
//!             | '*' name                           -- drop
//!             | '(' process ')'                    -- grouping
//!             | name '!' '(' process ')'           -- lift
//!             | name '(' ident ')' '.' term        -- input
//!             | NAME '(' args ')'                  -- macro application
//!             | ident                              -- alias / parameter use
//!             | name                               -- bare name (def-body only)
//! args      ::= ( process ( ',' process )* )?        -- positional
//!             | ident '<-' process ( ',' ident '<-' process )*   -- named
//! name      ::= '@' primary | ident
//! primary   ::= '0' | 'nil' | '*' name | '(' process ')'
//! ```
//!
//! A macro call is either all-positional (`f(A, B)`) or all-named
//! (`f(x <- A, y <- B)`, order-independent); the form is chosen by peeking for a
//! leading `ident '<-'`. Named routing to parameters (and the unknown/duplicate/
//! missing checks) happens in [`crate::resolve`]; here we only reject a mixed
//! call. Both forms are pure call-site sugar over the same expansion.
//!
//! The only other context-sensitivity is disambiguating `ident '(' … ')'`: it is
//! a macro application when `ident` is a declared macro (collected in a cheap
//! first pass, [`collect_macros`]), and an input prefix otherwise.

use std::collections::HashMap;

use crate::ast::{Args, Block, Def, NamedArg, Pos, S};
use crate::lexer::{Tok, Token};
use crate::ParseError;

/// A parsed file: the declaration table, each declaration's position (for
/// diagnostics such as cycle reports), and the program block.
pub(crate) struct Program {
    /// Collected `def` declarations, keyed by name.
    pub(crate) defs: HashMap<String, Def>,
    /// Declaration positions, keyed by name.
    pub(crate) decl_pos: HashMap<String, Pos>,
    /// The top-level `new`-preamble plus program term.
    pub(crate) program: Block,
}

/// The maximum recursion depth of the descent before the parser bails out with
/// a clean [`ParseError`] instead of overflowing the process stack.
///
/// The hand-written recursive-descent parser recurses once (or twice) per level
/// of source nesting — nested groups `((…))`, nested quotes `@(…)`, drops `*x`,
/// input/lift bodies, and parallel terms. On adversarial input (e.g. hundreds of
/// nested parentheses) an unbounded descent hits the platform stack limit and
/// aborts the process with an *uncatchable* `STATUS_STACK_OVERFLOW` (SIGSEGV on
/// Unix). Empirically the crash begins around 600–800 nested parens; a cap of
/// 256 sits comfortably below that (roughly a third of the observed limit, i.e.
/// ample stack headroom) yet astronomically above any real program — a genuine
/// protocol nests only a handful of levels deep — so no reasonable input is ever
/// rejected. The counter tracks descent-function entries, so a single level of
/// source nesting advances it by one or two; the cap is generous under either
/// accounting.
const MAX_DEPTH: usize = 256;

/// The parser state: the token stream, a cursor, the set of macro names
/// (declarations with a parameter list) used to disambiguate applications, and
/// the current recursion depth of the descent (see [`MAX_DEPTH`]).
pub(crate) struct Parser {
    toks: Vec<Token>,
    pos: usize,
    macros: std::collections::HashSet<String>,
    /// The current nesting depth of the recursive descent. Incremented on entry
    /// to each recursive parse function and decremented on exit; when it would
    /// exceed [`MAX_DEPTH`] the parser returns a "nesting too deep" error rather
    /// than recursing further and risking a stack overflow.
    depth: usize,
}

/// First pass: collect the names of all macros (a `def` with a `(`).
///
/// Knowing the macro names up front lets the second pass tell a macro
/// application `f(x)` from an input prefix `x(y).…`, regardless of declaration
/// order (macros may be used before they are declared).
fn collect_macros(toks: &[Token]) -> std::collections::HashSet<String> {
    let mut out = std::collections::HashSet::new();
    let mut i = 0;
    while i < toks.len() {
        if matches!(toks[i].kind, Tok::Def) {
            if let Some(Token {
                kind: Tok::Ident(name),
                ..
            }) = toks.get(i + 1)
            {
                if matches!(toks.get(i + 2).map(|t| &t.kind), Some(Tok::LParen)) {
                    out.insert(name.clone());
                }
            }
        }
        i += 1;
    }
    out
}

impl Parser {
    /// Create a parser over a lexed token stream (which must end in [`Tok::Eof`]).
    pub(crate) fn new(toks: Vec<Token>) -> Self {
        let macros = collect_macros(&toks);
        Parser {
            toks,
            pos: 0,
            macros,
            depth: 0,
        }
    }

    // --- recursion-depth guard ---------------------------------------------

    /// Enter one level of recursive descent, failing with a clean
    /// [`ParseError`] (anchored at the current token) if the nesting would
    /// exceed [`MAX_DEPTH`]. Every recursive parse function calls this on entry
    /// and pairs it with [`Parser::exit`] on the way out, so a normal (finite,
    /// shallow) program never trips it while an adversarially deep one is
    /// rejected before it can overflow the stack.
    fn enter(&mut self) -> Result<(), ParseError> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            Err(self.err_here(format!(
                "input nested too deeply (exceeded the maximum nesting depth of \
                 {MAX_DEPTH}); simplify or split the program"
            )))
        } else {
            Ok(())
        }
    }

    /// Leave one level of recursive descent (the counterpart to
    /// [`Parser::enter`]). Called on the success path so that sibling recursion
    /// (parallel terms, argument lists) does not accumulate depth.
    fn exit(&mut self) {
        self.depth -= 1;
    }

    // --- cursor helpers ----------------------------------------------------

    /// The kind of the current (not-yet-consumed) token.
    fn peek(&self) -> &Tok {
        &self.toks[self.pos].kind
    }

    /// The current token (kind + position).
    fn cur(&self) -> &Token {
        &self.toks[self.pos]
    }

    /// The `(line, column)` of the current token.
    fn cur_pos(&self) -> Pos {
        let t = self.cur();
        (t.line, t.col)
    }

    /// Advance past the current token, returning it. Never advances past
    /// [`Tok::Eof`].
    fn bump(&mut self) -> Token {
        let t = self.toks[self.pos].clone();
        if !matches!(t.kind, Tok::Eof) {
            self.pos += 1;
        }
        t
    }

    /// Build an error anchored at the current token's position.
    fn err_here(&self, message: impl Into<String>) -> ParseError {
        let t = self.cur();
        ParseError {
            line: t.line,
            column: t.col,
            message: message.into(),
        }
    }

    /// Consume the current token if it equals `want`, else error.
    fn expect(&mut self, want: &Tok, what: &str) -> Result<(), ParseError> {
        if self.peek() == want {
            self.bump();
            Ok(())
        } else {
            Err(self.err_here(format!("expected {what}, found {}", self.peek().describe())))
        }
    }

    /// Consume an identifier token, returning its text.
    fn expect_ident(&mut self, what: &str) -> Result<String, ParseError> {
        if let Tok::Ident(s) = &self.cur().kind {
            let s = s.clone();
            self.bump();
            Ok(s)
        } else {
            Err(self.err_here(format!("expected {what}, found {}", self.peek().describe())))
        }
    }

    // --- top level ---------------------------------------------------------

    /// Parse a whole file: declarations, then a single required program process.
    pub(crate) fn parse_file(&mut self) -> Result<Program, ParseError> {
        let mut defs: HashMap<String, Def> = HashMap::new();
        let mut decl_pos: HashMap<String, Pos> = HashMap::new();
        let mut top_news: Vec<(String, Pos)> = Vec::new();

        loop {
            match self.peek() {
                Tok::Def => {
                    let (name, pos, def) = self.parse_def()?;
                    if defs.contains_key(&name) {
                        return Err(ParseError {
                            line: pos.0,
                            column: pos.1,
                            message: format!("duplicate definition `{name}`"),
                        });
                    }
                    decl_pos.insert(name.clone(), pos);
                    defs.insert(name, def);
                }
                Tok::New => {
                    let names = self.parse_new()?;
                    top_news.extend(names);
                }
                _ => break,
            }
        }

        if matches!(self.peek(), Tok::Eof) {
            return Err(self.err_here(
                "expected a program process after the declarations \
                 (a file must end with exactly one process)",
            ));
        }
        let term = self.parse_process()?;
        self.expect(&Tok::Eof, "end of input")?;
        Ok(Program {
            defs,
            decl_pos,
            program: Block {
                news: top_news,
                term,
            },
        })
    }

    /// Parse a whole program that is a single name (used by
    /// [`crate::parse_name`]): a name followed by end of input.
    pub(crate) fn parse_name_program(&mut self) -> Result<S, ParseError> {
        let n = self.parse_name()?;
        self.expect(&Tok::Eof, "end of input")?;
        Ok(n)
    }

    // --- declarations ------------------------------------------------------

    /// `def ident ( '(' params ')' )? '{' block '}'`.
    fn parse_def(&mut self) -> Result<(String, Pos, Def), ParseError> {
        self.expect(&Tok::Def, "`def`")?;
        let pos = self.cur_pos();
        let name = self.expect_ident("a definition name after `def`")?;
        let params = if matches!(self.peek(), Tok::LParen) {
            self.bump();
            let ps = self.parse_params()?;
            self.expect(&Tok::RParen, "`)` to close the parameter list")?;
            Some(ps)
        } else {
            None
        };
        self.expect(&Tok::LBrace, "`{` to open the definition body")?;
        let body = self.parse_block()?;
        self.expect(&Tok::RBrace, "`}` to close the definition body")?;
        let def = match params {
            Some(params) => Def::Macro { params, body },
            None => Def::Alias(body),
        };
        Ok((name, pos, def))
    }

    /// A non-empty, comma-separated list of parameter identifiers.
    fn parse_params(&mut self) -> Result<Vec<String>, ParseError> {
        let mut out = vec![self.expect_ident("a parameter name")?];
        while matches!(self.peek(), Tok::Comma) {
            self.bump();
            out.push(self.expect_ident("a parameter name")?);
        }
        Ok(out)
    }

    /// `new ident ( ',' ident )*` — a run of ground-name declarations.
    fn parse_new(&mut self) -> Result<Vec<(String, Pos)>, ParseError> {
        self.expect(&Tok::New, "`new`")?;
        let mut out = Vec::new();
        let pos = self.cur_pos();
        out.push((self.expect_ident("a name to mint after `new`")?, pos));
        while matches!(self.peek(), Tok::Comma) {
            self.bump();
            let pos = self.cur_pos();
            out.push((self.expect_ident("a name to mint after `,`")?, pos));
        }
        Ok(out)
    }

    /// A braced definition body: local `new` declarations then a term.
    fn parse_block(&mut self) -> Result<Block, ParseError> {
        let mut news = Vec::new();
        while matches!(self.peek(), Tok::New) {
            news.extend(self.parse_new()?);
        }
        let term = self.parse_process()?;
        Ok(Block { news, term })
    }

    // --- processes ---------------------------------------------------------

    /// `process ::= term ( '|' term )*` — parallel composition, lowest precedence.
    ///
    /// A depth-guarded wrapper around [`Parser::parse_process_inner`]: it counts
    /// this level of the descent so pathologically nested input is rejected with
    /// a clean error instead of overflowing the stack.
    fn parse_process(&mut self) -> Result<S, ParseError> {
        self.enter()?;
        let r = self.parse_process_inner();
        self.exit();
        r
    }

    /// The body of [`Parser::parse_process`] (see it for the grammar); call that
    /// wrapper, not this, so the recursion-depth guard is applied.
    fn parse_process_inner(&mut self) -> Result<S, ParseError> {
        let mut items = vec![self.parse_term()?];
        while matches!(self.peek(), Tok::Bar) {
            self.bump();
            items.push(self.parse_term()?);
        }
        if items.len() == 1 {
            Ok(items.pop().expect("nonempty"))
        } else {
            Ok(S::Par(items))
        }
    }

    /// A single prefix-level term (binds tighter than `|`).
    ///
    /// A depth-guarded wrapper around [`Parser::parse_term_inner`].
    fn parse_term(&mut self) -> Result<S, ParseError> {
        self.enter()?;
        let r = self.parse_term_inner();
        self.exit();
        r
    }

    /// The body of [`Parser::parse_term`]; call the wrapper so the depth guard
    /// is applied.
    fn parse_term_inner(&mut self) -> Result<S, ParseError> {
        match self.peek() {
            Tok::Zero => {
                self.bump();
                Ok(S::Zero)
            }
            Tok::Star => {
                self.bump();
                Ok(S::Drop(Box::new(self.parse_name()?)))
            }
            Tok::LParen => {
                self.bump();
                let p = self.parse_process()?;
                self.expect(&Tok::RParen, "`)` to close the group")?;
                Ok(p)
            }
            Tok::At => {
                let chan = self.parse_name()?;
                self.after_channel(chan)
            }
            Tok::Ident(x) => {
                let x = x.clone();
                let pos = self.cur_pos();
                self.bump();
                match self.peek() {
                    Tok::Bang => self.parse_lift(S::Ident(x, pos)),
                    Tok::LParen if self.macros.contains(&x) => self.parse_call(x, pos),
                    Tok::LParen => self.parse_input(S::Ident(x, pos)),
                    // A bare identifier term: an alias or parameter used as a process.
                    _ => Ok(S::Ident(x, pos)),
                }
            }
            _ => Err(self.err_here(format!(
                "expected a process (`0`, `*x`, `x!(…)`, `x(y).…`, `f(…)`, or `( … )`), found {}",
                self.peek().describe()
            ))),
        }
    }

    /// After parsing a quote channel `@P`, dispatch on `!`/`(` (lift/input) or
    /// return the bare name (legal only as a definition body).
    fn after_channel(&mut self, chan: S) -> Result<S, ParseError> {
        match self.peek() {
            Tok::Bang => self.parse_lift(chan),
            Tok::LParen => self.parse_input(chan),
            _ => Ok(chan),
        }
    }

    /// `name '!' '(' process ')'` — a lift, with `chan` already parsed.
    fn parse_lift(&mut self, chan: S) -> Result<S, ParseError> {
        self.expect(&Tok::Bang, "`!`")?;
        self.expect(&Tok::LParen, "`(` to open the lifted process")?;
        let arg = self.parse_process()?;
        self.expect(&Tok::RParen, "`)` to close the lifted process")?;
        Ok(S::Lift {
            chan: Box::new(chan),
            arg: Box::new(arg),
        })
    }

    /// `name '(' ident ')' '.' term` — an input, with `chan` already parsed.
    fn parse_input(&mut self, chan: S) -> Result<S, ParseError> {
        self.expect(&Tok::LParen, "`(` to open the input binder")?;
        let bound = self.expect_ident("an identifier (the input binder)")?;
        self.expect(&Tok::RParen, "`)` to close the input binder")?;
        self.expect(&Tok::Dot, "`.` before the input continuation")?;
        let body = self.parse_term()?;
        Ok(S::Input {
            chan: Box::new(chan),
            bound,
            body: Box::new(body),
        })
    }

    /// `NAME '(' args ')'` — a macro application, with the name already consumed.
    ///
    /// Arguments are either **all positional** (`f(A, B, …)`) or **all named**
    /// (`f(p <- A, q <- B, …)`), never mixed. The form is chosen by peeking at
    /// the first argument: a leading `identifier '<-'` selects the named form,
    /// anything else the positional form. A bare `f(foo)` (identifier, no `<-`)
    /// therefore stays positional. Mixing the two forms is a loud error; unknown,
    /// duplicate, and missing parameter names are diagnosed later, in
    /// [`crate::resolve`], where the parameter list is known.
    fn parse_call(&mut self, name: String, pos: Pos) -> Result<S, ParseError> {
        self.expect(&Tok::LParen, "`(` to open the macro arguments")?;
        // An empty argument list is (trivially) positional.
        if matches!(self.peek(), Tok::RParen) {
            self.bump();
            return Ok(S::Call {
                name,
                args: Args::Positional(Vec::new()),
                pos,
            });
        }
        let args = if self.named_arg_ahead() {
            Args::Named(self.parse_named_args()?)
        } else {
            Args::Positional(self.parse_positional_args()?)
        };
        self.expect(&Tok::RParen, "`)` to close the macro arguments")?;
        Ok(S::Call { name, args, pos })
    }

    /// Whether the cursor sits at the start of a named argument: `identifier
    /// '<-'`. Used to pick the call form and to catch mixed forms.
    fn named_arg_ahead(&self) -> bool {
        matches!(self.peek(), Tok::Ident(_))
            && matches!(
                self.toks.get(self.pos + 1).map(|t| &t.kind),
                Some(Tok::Larrow)
            )
    }

    /// A comma-separated run of positional arguments (at least one).
    fn parse_positional_args(&mut self) -> Result<Vec<S>, ParseError> {
        let mut args = Vec::new();
        loop {
            // A `param <- …` here means the call started positional then switched.
            if self.named_arg_ahead() {
                return Err(self.err_here("cannot mix positional and named arguments"));
            }
            args.push(self.parse_process()?);
            if matches!(self.peek(), Tok::Comma) {
                self.bump();
            } else {
                break;
            }
        }
        Ok(args)
    }

    /// A comma-separated run of named `param <- arg` arguments (at least one).
    fn parse_named_args(&mut self) -> Result<Vec<NamedArg>, ParseError> {
        let mut args = Vec::new();
        loop {
            // Every argument of a named call must itself be `identifier '<-'`.
            if !self.named_arg_ahead() {
                return Err(self.err_here("cannot mix positional and named arguments"));
            }
            let pos = self.cur_pos();
            let param = self.expect_ident("a parameter name")?;
            self.expect(&Tok::Larrow, "`<-` after the parameter name")?;
            let value = self.parse_process()?;
            args.push(NamedArg { param, pos, value });
            if matches!(self.peek(), Tok::Comma) {
                self.bump();
            } else {
                break;
            }
        }
        Ok(args)
    }

    // --- names -------------------------------------------------------------

    /// `name ::= '@' primary | ident`.
    ///
    /// A depth-guarded wrapper around [`Parser::parse_name_inner`]; names can
    /// nest arbitrarily (`@*@*…`, `@(…)`), so this level is counted too.
    fn parse_name(&mut self) -> Result<S, ParseError> {
        self.enter()?;
        let r = self.parse_name_inner();
        self.exit();
        r
    }

    /// The body of [`Parser::parse_name`]; call the wrapper so the depth guard
    /// is applied.
    fn parse_name_inner(&mut self) -> Result<S, ParseError> {
        match self.peek() {
            Tok::At => {
                let pos = self.cur_pos();
                self.bump();
                let body = self.parse_primary()?;
                Ok(S::Quote(Box::new(body), pos))
            }
            Tok::Ident(x) => {
                let x = x.clone();
                let pos = self.cur_pos();
                self.bump();
                Ok(S::Ident(x, pos))
            }
            _ => Err(self.err_here(format!(
                "expected a name (`@P` or a bound identifier), found {}",
                self.peek().describe()
            ))),
        }
    }

    /// `primary ::= '0' | '*' name | '(' process ')'` — the tight process that
    /// may follow `@` without grouping.
    ///
    /// A depth-guarded wrapper around [`Parser::parse_primary_inner`].
    fn parse_primary(&mut self) -> Result<S, ParseError> {
        self.enter()?;
        let r = self.parse_primary_inner();
        self.exit();
        r
    }

    /// The body of [`Parser::parse_primary`]; call the wrapper so the depth
    /// guard is applied.
    fn parse_primary_inner(&mut self) -> Result<S, ParseError> {
        match self.peek() {
            Tok::Zero => {
                self.bump();
                Ok(S::Zero)
            }
            Tok::Star => {
                self.bump();
                Ok(S::Drop(Box::new(self.parse_name()?)))
            }
            Tok::LParen => {
                self.bump();
                let p = self.parse_process()?;
                self.expect(&Tok::RParen, "`)` to close the quoted group")?;
                Ok(p)
            }
            _ => Err(self.err_here(format!(
                "expected a process after `@` (one of `0`, `*x`, or `( … )`), found {}",
                self.peek().describe()
            ))),
        }
    }
}
