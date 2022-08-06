use log::debug;
use std::boxed::Box;
use std::collections::HashMap;

use crate::vm;

const DEFAULT_CALL_PRECEDENCE: usize = 0;

// #[derive(Debug)]
// pub struct Location {
//     // how many characters have been seen since the begining of
//     // parsing
//     cursor: usize,
//     // how many end-of-line sequences seen since the begining of
//     // parsing
//     line: usize,
//     // how many characters seen since the begining of the line
//     column: usize,
// }

#[derive(Clone, Debug, Hash, PartialEq)]
pub enum AST {
    Grammar(Vec<AST>),
    Definition(String, Box<AST>),
    LabelDefinition(String, String),
    Sequence(Vec<AST>),
    Choice(Vec<AST>),
    Not(Box<AST>),
    Optional(Box<AST>),
    ZeroOrMore(Box<AST>),
    OneOrMore(Box<AST>),
    Identifier(String),
    Str(String),
    Range(char, char),
    Char(char),
    Label(String, Box<AST>),
    Any,
    Empty,
}

#[derive(Debug)]
pub struct Fun {
    name: String,
    addr: usize,
    size: usize,
}

#[derive(Debug)]
pub struct Compiler {
    // The index of the last instruction written the `code` vector
    cursor: usize,
    // Vector where the compiler writes down the instructions
    code: Vec<vm::Instruction>,
    // Storage for unique (interned) strings
    strings: Vec<String>,
    // Map from strings to their position in the `strings` vector
    strings_map: HashMap<String, usize>,
    // Map from set of production string ids to the set of metadata
    // about the production
    funcs: HashMap<usize, Fun>,
    // Map from set of positions of the first instruction of rules to
    // the position of their index in the strings map
    identifiers: HashMap<usize, usize>,
    // Map from call site addresses to production names that keeps
    // calls that need to be patched because they occurred syntaticaly
    // before the definition of the production
    addrs: HashMap<usize /* addr */, usize /* string id */>,
    // Map from the set of labels to the set of messages for error
    // reporting
    labels: HashMap<usize, usize>,
    // Map from the set of label IDs to the set with the first address
    // of the label's respective recovery expression
    recovery: HashMap<usize, usize>,
    // Used for printing out debugging messages with the of the
    // structure the call stack the compiler is traversing
    indent_level: usize,
}

impl Compiler {
    pub fn new() -> Self {
        Compiler {
            cursor: 0,
            code: vec![],
            strings: vec![],
            strings_map: HashMap::new(),
            identifiers: HashMap::new(),
            funcs: HashMap::new(),
            addrs: HashMap::new(),
            labels: HashMap::new(),
            recovery: HashMap::new(),
            indent_level: 0,
        }
    }

    /// Takes a PEG string and runs the compilation process, by
    /// parsing the input string, traversing the output grammar to
    /// emit the code, and then backpatching both call sites deferred
    /// during the code main generation pass.
    pub fn compile_str(&mut self, s: &str) -> Result<(), Error> {
        let mut p = Parser::new(s);
        self.compile(p.parse_grammar()?)?;
        self.backpatch_callsites()?;
        Ok(())
    }

    /// Access the output of the compilation process.  Call this
    /// method after calling `compile_str()`.
    pub fn program(self) -> vm::Program {
        vm::Program::new(
            self.identifiers,
            self.labels,
            self.recovery,
            self.strings,
            self.code,
        )
    }

    /// Try to find the string `s` within the table of interned
    /// strings, and return its ID if it is found.  If the string `s`
    /// doesn't exist within the interned table yet, it's inserted and
    /// the index where it was inserted becomes its ID.
    fn push_string(&mut self, s: String) -> usize {
        let strid = self.strings.len();
        if let Some(id) = self.strings_map.get(&s) {
            return *id;
        }
        self.strings.push(s.clone());
        self.strings_map.insert(s, strid);
        strid
    }

    /// Iterate over the set of addresses of call sites of forward
    /// rule declarations and re-emit the `Call` opcode with the right
    /// offset that could not be figured out in the first pass of the
    /// compilation.
    fn backpatch_callsites(&mut self) -> Result<(), Error> {
        for (addr, id) in &self.addrs {
            match self.funcs.get(id) {
                Some(func) => {
                    if func.addr > *addr {
                        self.code[*addr] = vm::Instruction::Call(func.addr - addr, DEFAULT_CALL_PRECEDENCE);
                    } else {
                        self.code[*addr] = vm::Instruction::CallB(addr - func.addr, DEFAULT_CALL_PRECEDENCE);
                    }
                }
                None => {
                    let name = self.strings[*id].clone();
                    return Err(Error::CompileError(format!(
                        "Production {:?} doesnt exist",
                        name
                    )));
                }
            }
        }
        Ok(())
    }

    fn compile(&mut self, node: AST) -> Result<(), Error> {
        match node {
            AST::Grammar(rules) => {
                self.emit(vm::Instruction::Call(2, DEFAULT_CALL_PRECEDENCE));
                self.emit(vm::Instruction::Halt);
                for r in rules {
                    self.compile(r)?;
                }
                Ok(())
            }
            AST::Definition(name, expr) => {
                let addr = self.cursor;
                let strid = self.push_string(name.clone());
                self.identifiers.insert(addr, strid);
                self.compile(*expr)?;
                self.emit(vm::Instruction::Return);

                let size = self.cursor - addr;
                self.funcs.insert(strid, Fun { name, addr, size });
                Ok(())
            }
            AST::LabelDefinition(name, message) => {
                let name_id = self.push_string(name);
                let message_id = self.push_string(message);
                self.labels.insert(name_id, message_id);
                Ok(())
            }
            AST::Label(name, element) => {
                let label_id = self.push_string(name);
                let pos = self.cursor;
                self.emit(vm::Instruction::Choice(0));
                self.compile(*element)?;
                self.code[pos] = vm::Instruction::Choice(self.cursor - pos + 1);
                self.emit(vm::Instruction::Commit(2));
                self.emit(vm::Instruction::Throw(label_id));
                Ok(())
            }
            AST::Sequence(seq) => {
                self.indent("Seq");
                for s in seq.into_iter() {
                    self.compile(s)?;
                }
                self.dedent("Seq");
                Ok(())
            }
            AST::Optional(op) => {
                let pos = self.cursor;
                self.emit(vm::Instruction::Choice(0));
                self.compile(*op)?;
                let size = self.cursor - pos;
                self.code[pos] = vm::Instruction::Choice(size + 1);
                self.emit(vm::Instruction::Commit(1));
                Ok(())
            }
            AST::Choice(choices) => {
                let (mut i, last_choice) = (0, choices.len() - 1);
                let mut commits = vec![];

                for choice in choices {
                    if i == last_choice {
                        self.compile(choice)?;
                        break;
                    }
                    i += 1;
                    let pos = self.cursor;
                    self.emit(vm::Instruction::Choice(0));
                    self.compile(choice)?;
                    self.code[pos] = vm::Instruction::Choice(self.cursor - pos + 1);
                    commits.push(self.cursor);
                    self.emit(vm::Instruction::Commit(0));
                }

                for commit in commits {
                    self.code[commit] = vm::Instruction::Commit(self.cursor - commit);
                }

                Ok(())
            }
            AST::Not(expr) => {
                let pos = self.cursor;
                self.emit(vm::Instruction::ChoiceP(0));
                self.compile(*expr)?;
                self.code[pos] = vm::Instruction::ChoiceP(self.cursor - pos + 2);
                self.emit(vm::Instruction::Commit(1));
                self.emit(vm::Instruction::Fail);
                Ok(())
            }
            AST::ZeroOrMore(expr) => {
                let pos = self.cursor;
                self.emit(vm::Instruction::Choice(0));
                self.compile(*expr)?;
                let size = self.cursor - pos;
                self.code[pos] = vm::Instruction::Choice(size + 1);
                self.emit(vm::Instruction::CommitB(size));
                Ok(())
            }
            AST::OneOrMore(expr) => {
                let e = *expr;
                self.compile(e.clone())?;
                let pos = self.cursor;
                self.emit(vm::Instruction::Choice(0));
                self.compile(e)?;
                self.code[pos] = vm::Instruction::Choice(self.cursor - pos + 1);
                self.emit(vm::Instruction::CommitB(self.cursor - pos));
                Ok(())
            }
            AST::Identifier(name) => {
                let id = self.push_string(name);
                match self.funcs.get(&id) {
                    Some(func) => {
                        let addr = self.cursor - func.addr;
                        self.emit(vm::Instruction::CallB(addr, DEFAULT_CALL_PRECEDENCE));
                    }
                    None => {
                        self.addrs.insert(self.cursor, id);
                        self.emit(vm::Instruction::Call(0, DEFAULT_CALL_PRECEDENCE));
                    }
                }
                self.emit(vm::Instruction::Capture);
                Ok(())
            }
            AST::Range(a, b) => {
                self.emit(vm::Instruction::Span(a, b));
                self.emit(vm::Instruction::Capture);
                Ok(())
            }
            AST::Str(s) => {
                let id = self.push_string(s);
                self.emit(vm::Instruction::Str(id));
                self.emit(vm::Instruction::Capture);
                Ok(())
            }
            AST::Char(c) => {
                self.emit(vm::Instruction::Char(c));
                self.emit(vm::Instruction::Capture);
                Ok(())
            }
            AST::Any => {
                self.emit(vm::Instruction::Any);
                self.emit(vm::Instruction::Capture);
                Ok(())
            }
            AST::Empty => Ok(()),
        }
    }

    fn emit(&mut self, instruction: vm::Instruction) {
        self.prt(format!("emit {:?} {:?}", self.cursor, instruction).as_str());
        self.code.push(instruction);
        self.cursor += 1;
    }

    // Debugging helpers

    fn prt(&mut self, msg: &str) {
        debug!("{:indent$}{}", "", msg, indent = self.indent_level);
    }

    fn indent(&mut self, msg: &str) {
        debug!("{:width$}Open {}", "", msg, width = self.indent_level);
        self.indent_level += 2;
    }

    fn dedent(&mut self, msg: &str) {
        self.indent_level -= 2;
        debug!("{:width$}Close {}", "", msg, width = self.indent_level);
    }
}

impl Default for Compiler {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
pub enum Error {
    BacktrackError(usize, String),
    CompileError(String),
    // ParseError(String),
}

impl std::error::Error for Error {}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::BacktrackError(i, m) => write!(f, "Syntax Error: {}: {}", i, m),
            Error::CompileError(m) => write!(f, "Compile Error: {}", m),
        }
    }
}

pub struct Parser {
    cursor: usize,
    ffp: usize,
    source: Vec<char>,
}

type ParseFn<T> = fn(&mut Parser) -> Result<T, Error>;

impl Parser {
    pub fn new(s: &str) -> Self {
        return Parser {
            cursor: 0,
            ffp: 0,
            source: s.chars().collect(),
        };
    }

    // GR: Grammar <- Spacing (Definition / LabelDefinition)+ EndOfFile
    pub fn parse_grammar(&mut self) -> Result<AST, Error> {
        self.parse_spacing()?;
        let defs = self.one_or_more(|p| {
            p.choice(vec![|p| p.parse_label_definition(), |p| {
                p.parse_definition()
            }])
        })?;
        self.parse_eof()?;
        Ok(AST::Grammar(defs))
    }

    // GR: Definition <- Identifier LEFTARROW Expression
    fn parse_definition(&mut self) -> Result<AST, Error> {
        let id = self.parse_identifier()?;
        self.expect('<')?;
        self.expect('-')?;
        self.parse_spacing()?;
        let expr = self.parse_expression()?;
        Ok(AST::Definition(id, Box::new(expr)))
    }

    // GR: LabelDefinition <- LABEL Identifier EQ Literal
    fn parse_label_definition(&mut self) -> Result<AST, Error> {
        self.expect_str("label")?;
        self.parse_spacing()?;
        let label = self.parse_identifier()?;
        self.expect('=')?;
        self.parse_spacing()?;
        let literal = self.parse_literal()?;
        Ok(AST::LabelDefinition(label, literal))
    }

    // GR: Expression <- Sequence (SLASH Sequence)*
    fn parse_expression(&mut self) -> Result<AST, Error> {
        let first = self.parse_sequence()?;
        let mut choices = vec![first];
        choices.append(&mut self.zero_or_more(|p| {
            p.expect('/')?;
            p.parse_spacing()?;
            p.parse_sequence()
        })?);
        Ok(if choices.len() == 1 {
            choices.remove(0)
        } else {
            AST::Choice(choices)
        })
    }

    // GR: Sequence <- Prefix*
    fn parse_sequence(&mut self) -> Result<AST, Error> {
        let seq = self.zero_or_more(|p| p.parse_prefix())?;
        Ok(AST::Sequence(if seq.is_empty() {
            vec![AST::Empty]
        } else {
            seq
        }))
    }

    // GR: Prefix <- (AND / NOT)? Labeled
    fn parse_prefix(&mut self) -> Result<AST, Error> {
        let prefix = self.choice(vec![
            |p| {
                p.expect_str("&")?;
                p.parse_spacing()?;
                Ok("&")
            },
            |p| {
                p.expect_str("!")?;
                p.parse_spacing()?;
                Ok("!")
            },
            |_| Ok(""),
        ]);
        let labeled = self.parse_labeled()?;
        Ok(match prefix {
            Ok("&") => AST::Not(Box::new(AST::Not(Box::new(labeled)))),
            Ok("!") => AST::Not(Box::new(labeled)),
            _ => labeled,
        })
    }

    // GR: Labeled <- Suffix Label?
    fn parse_labeled(&mut self) -> Result<AST, Error> {
        let suffix = self.parse_suffix()?;
        Ok(match self.parse_label() {
            Ok(label) => AST::Label(label, Box::new(suffix)),
            _ => suffix,
        })
    }

    // GR: Label   <- [^⇑] Identifier
    fn parse_label(&mut self) -> Result<String, Error> {
        self.choice(vec![|p| p.expect_str("^"), |p| p.expect_str("⇑")])?;
        self.parse_identifier()
    }

    // GR: Suffix  <- Primary (QUESTION / STAR / PLUS)?
    fn parse_suffix(&mut self) -> Result<AST, Error> {
        let primary = self.parse_primary()?;
        let suffix = self.choice(vec![
            |p| {
                p.expect_str("?")?;
                p.parse_spacing()?;
                Ok("?")
            },
            |p| {
                p.expect_str("*")?;
                p.parse_spacing()?;
                Ok("*")
            },
            |p| {
                p.expect_str("+")?;
                p.parse_spacing()?;
                Ok("+")
            },
            |_| Ok(""),
        ]);
        Ok(match suffix {
            Ok("?") => AST::Optional(Box::new(primary)),
            Ok("*") => AST::ZeroOrMore(Box::new(primary)),
            Ok("+") => AST::OneOrMore(Box::new(primary)),
            _ => primary,
        })
    }

    // GR: Primary <- Identifier !(LEFTARROW / (Identifier EQ))
    // GR:          / OPEN Expression CLOSE
    // GR:          / Literal / Class / DOT
    fn parse_primary(&mut self) -> Result<AST, Error> {
        self.choice(vec![
            |p| {
                let id = p.parse_identifier()?;
                p.not(|p| {
                    p.expect('<')?;
                    p.expect('-')?;
                    p.parse_spacing()
                })?;
                p.not(|p| {
                    p.parse_identifier()?;
                    p.expect('=')?;
                    p.parse_spacing()
                })?;
                Ok(AST::Identifier(id))
            },
            |p| {
                p.expect('(')?;
                p.parse_spacing()?;
                let expr = p.parse_expression()?;
                p.expect(')')?;
                p.parse_spacing()?;
                Ok(expr)
            },
            |p| Ok(AST::Str(p.parse_literal()?)),
            |p| Ok(AST::Choice(p.parse_class()?)),
            |p| {
                p.parse_dot()?;
                Ok(AST::Any)
            },
        ])
    }

    // GR: Identifier <- IdentStart IdentCont* Spacing
    // GR: IdentStart <- [a-zA-Z_]
    // GR: IdentCont <- IdentStart / [0-9]
    fn parse_identifier(&mut self) -> Result<String, Error> {
        let ident_start = self.choice(vec![
            |p| p.expect_range('a', 'z'),
            |p| p.expect_range('A', 'Z'),
            |p| p.expect('_'),
        ])?;
        let ident_cont = self.zero_or_more(|p| {
            p.choice(vec![
                |p| p.expect_range('a', 'z'),
                |p| p.expect_range('A', 'Z'),
                |p| p.expect_range('0', '9'),
                |p| p.expect('_'),
            ])
        })?;
        self.parse_spacing()?;
        let cont_str: String = ident_cont.into_iter().collect();
        let id = format!("{}{}", ident_start, cont_str);
        Ok(id)
    }

    // GR: Literal <- [’] (![’]Char)* [’] Spacing
    // GR:          / ["] (!["]Char)* ["] Spacing
    fn parse_literal(&mut self) -> Result<String, Error> {
        self.choice(vec![|p| p.parse_simple_quote(), |p| p.parse_double_quote()])
    }

    fn parse_simple_quote(&mut self) -> Result<String, Error> {
        self.expect('\'')?;
        let r = self
            .zero_or_more(|p| {
                p.not(|p| p.expect('\''))?;
                p.parse_char()
            })?
            .into_iter()
            .collect();
        self.expect('\'')?;
        self.parse_spacing()?;
        Ok(r)
    }

    // TODO: duplicated the above code as I can't pass the quote as a
    // parameter to a more generic function. The `zero_or_more` parser
    // and all the other parsers expect a function pointer, not a
    // closure, and ~const Q: &'static str~ isn't allowed by default.
    fn parse_double_quote(&mut self) -> Result<String, Error> {
        self.expect('"')?;
        let r = self
            .zero_or_more(|p| {
                p.not(|p| p.expect('"'))?;
                p.parse_char()
            })?
            .into_iter()
            .collect();
        self.expect('"')?;
        self.parse_spacing()?;
        Ok(r)
    }

    // GR: Class <- ’[’ (!’]’Range)* ’]’ Spacing
    fn parse_class(&mut self) -> Result<Vec<AST>, Error> {
        self.expect('[')?;
        let output = self.zero_or_more::<AST>(|p| {
            p.not(|pp| pp.expect(']'))?;
            p.parse_range()
        });
        self.expect(']')?;
        self.parse_spacing()?;
        output
    }

    // GR: Range <- Char ’-’ Char / Char
    fn parse_range(&mut self) -> Result<AST, Error> {
        self.choice(vec![
            |p| {
                let left = p.parse_char()?;
                p.expect('-')?;
                Ok(AST::Range(left, p.parse_char()?))
            },
            |p| Ok(AST::Char(p.parse_char()?)),
        ])
    }

    // GR: Char <- ’\\’ [nrt’"\[\]\\]
    // GR:       / ’\\’ [0-2][0-7][0-7]
    // GR:       / ’\\’ [0-7][0-7]?
    // GR:       / !’\\’ .
    fn parse_char(&mut self) -> Result<char, Error> {
        self.choice(vec![|p| p.parse_char_escaped(), |p| {
            p.parse_char_non_escaped()
        }])
    }

    // ’\\’ [nrt’"\[\]\\]
    fn parse_char_escaped(&mut self) -> Result<char, Error> {
        self.expect('\\')?;
        self.choice(vec![
            |p| {
                p.expect('n')?;
                Ok('\n')
            },
            |p| {
                p.expect('r')?;
                Ok('\r')
            },
            |p| {
                p.expect('t')?;
                Ok('\t')
            },
            |p| {
                p.expect('\'')?;
                Ok('\'')
            },
            |p| {
                p.expect('"')?;
                Ok('\"')
            },
            |p| {
                p.expect(']')?;
                Ok(']')
            },
            |p| {
                p.expect('[')?;
                Ok('[')
            },
            |p| {
                p.expect('\\')?;
                Ok('\\')
            },
            |p| {
                p.expect('\'')?;
                Ok('\'')
            },
            |p| {
                p.expect('"')?;
                Ok('"')
            },
        ])
    }

    // !’\\’ .
    fn parse_char_non_escaped(&mut self) -> Result<char, Error> {
        self.not(|p| p.expect('\\'))?;
        self.any()
    }

    // GR: DOT <- '.' Spacing
    fn parse_dot(&mut self) -> Result<char, Error> {
        let r = self.expect('.')?;
        self.parse_spacing()?;
        Ok(r)
    }

    // GR: Spacing <- (Space/ Comment)*
    fn parse_spacing(&mut self) -> Result<(), Error> {
        self.zero_or_more(|p| p.choice(vec![|p| p.parse_space(), |p| p.parse_comment()]))?;
        Ok(())
    }

    // GR: Comment <- ’#’ (!EndOfLine.)* EndOfLine
    fn parse_comment(&mut self) -> Result<(), Error> {
        self.expect('#')?;
        self.zero_or_more(|p| {
            p.not(|p| p.parse_eol())?;
            p.any()
        })?;
        self.parse_eol()
    }

    // GR: Space <- ’ ’ / ’\t’ / EndOfLine
    fn parse_space(&mut self) -> Result<(), Error> {
        self.choice(vec![
            |p| {
                p.expect(' ')?;
                Ok(())
            },
            |p| {
                p.expect('\t')?;
                Ok(())
            },
            |p| p.parse_eol(),
        ])
    }

    // EndOfLine <- ’\r\n’ / ’\n’ / ’\r’
    fn parse_eol(&mut self) -> Result<(), Error> {
        self.choice(vec![
            |p| {
                p.expect('\r')?;
                p.expect('\n')
            },
            |p| p.expect('\n'),
            |p| p.expect('\r'),
        ])?;
        Ok(())
    }

    // EndOfFile <- !.
    fn parse_eof(&mut self) -> Result<(), Error> {
        self.not(|p| p.current())?;
        Ok(())
    }

    fn choice<T>(&mut self, funcs: Vec<ParseFn<T>>) -> Result<T, Error> {
        let cursor = self.cursor;
        for func in &funcs {
            match func(self) {
                Ok(o) => return Ok(o),
                Err(_) => self.cursor = cursor,
            }
        }
        Err(self.err("CHOICE".to_string()))
    }

    fn not<T>(&mut self, func: ParseFn<T>) -> Result<(), Error> {
        let cursor = self.cursor;
        let out = func(self);
        self.cursor = cursor;
        match out {
            Err(_) => Ok(()),
            Ok(_) => Err(self.err("NOT".to_string())),
        }
    }

    fn one_or_more<T>(&mut self, func: ParseFn<T>) -> Result<Vec<T>, Error> {
        let mut output = vec![func(self)?];
        output.append(&mut self.zero_or_more::<T>(func)?);
        Ok(output)
    }

    fn zero_or_more<T>(&mut self, func: ParseFn<T>) -> Result<Vec<T>, Error> {
        let mut output = vec![];
        loop {
            match func(self) {
                Ok(ch) => output.push(ch),
                Err(e) => match e {
                    Error::BacktrackError(..) => break,
                    _ => return Err(e),
                },
            }
        }
        Ok(output)
    }

    fn expect_range(&mut self, a: char, b: char) -> Result<char, Error> {
        let current = self.current()?;
        if current >= a && current <= b {
            self.next();
            return Ok(current);
        }
        Err(self.err(format!(
            "Expected char between `{}' and `{}' but got `{}' instead",
            a, b, current
        )))
    }

    fn expect_str(&mut self, expected: &str) -> Result<String, Error> {
        for c in expected.chars() {
            self.expect(c)?;
        }
        Ok(expected.to_string())
    }

    fn expect(&mut self, expected: char) -> Result<char, Error> {
        let current = self.current()?;
        if current == expected {
            self.next();
            return Ok(current);
        }
        Err(self.err(format!(
            "Expected `{}' but got `{}' instead",
            expected, current
        )))
    }

    fn any(&mut self) -> Result<char, Error> {
        let current = self.current()?;
        self.next();
        Ok(current)
    }

    fn current(&mut self) -> Result<char, Error> {
        if !self.eof() {
            return Ok(self.source[self.cursor]);
        }
        Err(self.err("EOF".to_string()))
    }

    fn eof(&self) -> bool {
        self.cursor == self.source.len()
    }

    fn next(&mut self) {
        self.cursor += 1;

        if self.cursor > self.ffp {
            self.ffp = self.cursor;
        }
    }

    fn err(&mut self, msg: String) -> Error {
        Error::BacktrackError(self.ffp, msg)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structure_empty() {
        let mut p = Parser::new(
            "A <- 'a' /
             B <- 'b'
            ",
        );
        let out = p.parse_grammar();

        assert!(out.is_ok());
        assert_eq!(
            AST::Grammar(vec![
                AST::Definition(
                    "A".to_string(),
                    Box::new(AST::Choice(vec![
                        AST::Sequence(vec![AST::Str("a".to_string())]),
                        AST::Sequence(vec![AST::Empty])
                    ]))
                ),
                AST::Definition(
                    "B".to_string(),
                    Box::new(AST::Sequence(vec![AST::Str("b".to_string())])),
                ),
            ]),
            out.unwrap()
        );
    }

    #[test]
    fn choice_pick_none() -> Result<(), Error> {
        let mut parser = Parser::new("e");
        let out = parser.choice(vec![
            |p| p.expect('a'),
            |p| p.expect('b'),
            |p| p.expect('c'),
            |p| p.expect('d'),
        ]);

        assert!(out.is_err());
        assert_eq!(0, parser.cursor);

        Ok(())
    }

    #[test]
    fn choice_pick_last() -> Result<(), Error> {
        let mut parser = Parser::new("d");
        let out = parser.choice(vec![
            |p| p.expect('a'),
            |p| p.expect('b'),
            |p| p.expect('c'),
            |p| p.expect('d'),
        ]);

        assert!(out.is_ok());
        assert_eq!(1, parser.cursor);

        Ok(())
    }

    #[test]
    fn choice_pick_first() -> Result<(), Error> {
        let mut parser = Parser::new("a");
        let out = parser.choice(vec![|p| p.expect('a')]);

        assert!(out.is_ok());
        assert_eq!(1, parser.cursor);

        Ok(())
    }

    #[test]
    fn not_success_on_err() -> Result<(), Error> {
        let mut parser = Parser::new("a");
        let out = parser.not(|p| p.expect('b'));

        assert!(out.is_ok());
        assert_eq!(0, parser.cursor);

        Ok(())
    }

    #[test]
    fn not_err_on_match() -> Result<(), Error> {
        let mut parser = Parser::new("a");
        let out = parser.not(|p| p.expect('a'));

        assert!(out.is_err());
        assert_eq!(0, parser.cursor);

        Ok(())
    }

    #[test]
    fn zero_or_more() -> Result<(), Error> {
        let mut parser = Parser::new("ab2");

        let prefix = parser.zero_or_more::<char>(|p| p.expect_range('a', 'z'))?;

        assert_eq!(vec!['a', 'b'], prefix);
        assert_eq!(2, parser.cursor);

        Ok(())
    }
}
