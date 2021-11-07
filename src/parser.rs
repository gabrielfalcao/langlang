use log::debug;
use std::boxed::Box;
use std::collections::HashMap;

use crate::vm;

#[derive(Debug)]
pub struct Location {
    // how many characters have been seen since the begining of
    // parsing
    cursor: usize,
    // how many end-of-line sequences seen since the begining of
    // parsing
    line: usize,
    // how many characters seen since the begining of the line
    column: usize,
}

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
pub enum AnnotationAlgo {
    Standard,
    // Updated,
}

#[derive(Debug)]
pub struct Config {
    annotation: Option<AnnotationAlgo>,
}

impl Default for Config {
    fn default() -> Self {
        Config { annotation: None }
    }
}

impl Config {
    pub fn new_with_standard_errlabels() -> Self {
        Config {
            annotation: Some(AnnotationAlgo::Standard),
        }
    }
}

#[derive(Debug)]
pub struct Compiler {
    // Tweak some knobs within the compiler
    config: Config,
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

impl Default for Compiler {
    fn default() -> Self {
        Self::new_with_config(Config::default())
    }
}

impl Compiler {
    pub fn new_with_config(config: Config) -> Self {
        Compiler {
            config,
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
    /// emit the code, and then backpatching both call sites and
    /// follows sets deferred during the code main generation pass.
    pub fn compile_str(&mut self, s: &str) -> Result<(), Error> {
        let mut p = Parser::new(s);
        let grammar = p.parse_grammar()?;
        let grammar = match self.config.annotation {
            None => grammar,
            Some(AnnotationAlgo::Standard) => StandardAlgorithm::new().traverse(grammar)?,
        };
        self.compile(grammar)?;
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
                        self.code[*addr] = vm::Instruction::Call(func.addr - addr, 0);
                    } else {
                        self.code[*addr] = vm::Instruction::CallB(addr - func.addr, 0);
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

    /// Traverse AST node and emit bytecode
    ///
    /// Bytecode for the Parsing Expression Grammars virtual machine.
    /// This work is heavily based on the article "A Parsing Machine
    /// for PEGs" by S. Medeiros, et al.
    ///
    /// The output of the compilation can be accessed via the
    /// `program()` method.
    fn compile(&mut self, node: AST) -> Result<(), Error> {
        match node {
            AST::Grammar(rules) => {
                self.emit(vm::Instruction::Call(2, 0));
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
                self.funcs.insert(
                    strid,
                    Fun {
                        name,
                        addr,
                        size: self.cursor - addr,
                    },
                );
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
                for s in seq {
                    self.compile(s)?;
                }
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
                        self.emit(vm::Instruction::CallB(addr, 0));
                    }
                    None => {
                        self.addrs.insert(self.cursor, id);
                        self.emit(vm::Instruction::Call(0, 0));
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
        debug!("emit {:?} {:?}", self.cursor, instruction);
        self.code.push(instruction);
        self.cursor += 1;
    }
}

/// Generic traversal for AST nodes, typed so it can be stored and
/// passed around.  The compiler can then be parametrized to take
/// different paths and execute different sets of transformation steps
/// depending on the set of input flags.
trait Traversal {
    fn traverse(&mut self, ast: AST) -> Result<AST, Error>;
}

#[derive(Clone, Debug)]
pub enum Token {
    // Deferred(usize),
// StringID(usize),
}

/// The Standard Algorithm takes a grammar G as input and outputs an
/// augumented grammar G' automatically annotated with labeled
/// failures.
#[derive(Debug)]
struct StandardAlgorithm {
    stage1: Stage1,
    firsts: HashMap<AST, Vec<Token>>,
    follows: HashMap<usize, Vec<Token>>,
    recovery: HashMap<usize, AST>,
    nullable: HashMap<AST, bool>,
    eat_tokens: AST,
    last_label_id: usize,
}

impl Traversal for StandardAlgorithm {
    fn traverse(&mut self, ast: AST) -> Result<AST, Error> {
        // traverse the AST once
        self.stage1.run(&ast);

        if !self.stage1.lexical_tokens.is_empty() {
            self.eat_tokens = AST::Choice(self.stage1.lexical_tokens.clone());
        }

        // traverse the ast one last time, building the result AST
        self.labelexp(ast)
    }
}

impl StandardAlgorithm {
    fn new() -> Self {
        // TODO: This hardcoded vector could come from configuration
        // forwarded by the Compiler
        let space_rules = vec!["Comment".to_string(), "Spacing".to_string()];

        StandardAlgorithm {
            stage1: Stage1::new_with_space_rules(space_rules),
            firsts: HashMap::new(),
            follows: HashMap::new(),
            nullable: HashMap::new(),
            recovery: HashMap::new(),
            eat_tokens: AST::Empty,
            last_label_id: 0,
        }
    }

    fn labelexp(&self, node: AST) -> Result<AST, Error> {
        match node {
            AST::Grammar(rules) => Ok(AST::Grammar(
                // recursive loop to resolve each Definition
                rules
                    .into_iter()
                    .map(|item| self.labelexp(item))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            AST::Definition(name, expr) => {
                // lexical rules don't get annotated
                if self.stage1.is_lex_rule(&name) {
                    Ok(AST::Definition(name, expr))
                } else {
                    Ok(self.labelexp_traverse(AST::Definition(name, expr), false)?)
                }
            }
            n @ _ => Ok(n),
        }
    }

    fn labelexp_traverse(&self, node: AST, seq: bool) -> Result<AST, Error> {
        match node {
            AST::Identifier(id) => {
                Ok(AST::Identifier(id))
            },
            AST::Sequence(s) => Ok(AST::Sequence(
                s.into_iter()
                    .map(|item| self.labelexp_traverse(item, seq))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            AST::Choice(choices) => Ok(AST::Choice(
                choices
                    .into_iter()
                    .map(|item| self.labelexp_traverse(item, seq))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            _ => Ok(node)
            // AST::Not(expr) => Ok(AST::Not(expr)),
            // AST::ZeroOrMore(expr) => Ok(AST::ZeroOrMore(Box::new(self.labelexp(*expr)?))),
            // AST::OneOrMore(expr) => Ok(AST::OneOrMore(Box::new(self.labelexp(*expr)?))),
            // AST::Identifier(name) => Ok(AST::Identifier(name)),
            // AST::Range(a, b) => Ok(AST::Range(a, b)),
            // AST::Str(s) => Ok(AST::Str(s)),
            // AST::Char(c) => Ok(AST::Char(c)),
            // AST::Any => Ok(AST::Any),
        }
    }

    // fn calck(&self, p: AST, follows: Vec<Token>) -> Vec<Token> {
    //     vec![]
    // }

    // fn new_label(&mut self) -> usize {
    //     self.last_label_id += 1;
    //     self.last_label_id
    // }

    // fn add_label(&mut self, p: AST, follows: Vec<Token>) -> AST {
    //     let label_id = self.new_label();
    //     self.recovery.insert(
    //         label_id,
    //         AST::ZeroOrMore(Box::new(AST::Sequence(vec![
    //             // AST::Not(Box::new(follows.map(|_| AST::Str("_".to_string())))),
    //             AST::Identifier("__eatToken__".to_string()),
    //         ]))),
    //     );
    //     AST::Label(format!("label{}", label_id), Box::new(p))
    // }
}

#[derive(Debug)]
/// The first stage of the StandardAlgorithm
///
/// This traversal collects following information:
///
/// 1. all the AST nodes with matchers for recognizable terminals
/// (`Char`, `Str`, and `Range`).  That's used for building the
/// `eatToken` expression.
///
/// 2. the names of rules that match exclusively white space
/// characters or call out identifiers of other rules that match
/// exclusively white spaces. e.g.:
///
/// ```
/// _   <- ws*
/// ws  <- eol / sp
/// eol <- '\n' / '\r\n' / '\r'
/// sp  <- [ \t]
/// ```
///
/// All the rules above would appear in the result of this function as
/// space rules.  The rules `_` and `ws` are examples of rules that
/// contain identifiers, but are still considered space rules because
/// the identifiers they call out to are rules that only match space
/// characters (`eol` and `sp`).
///
/// 3. the names of rules that contain expressions that match
/// syntatical structure. Notice that space rules don't ever appear on
/// this list. e.g.:
///
/// ```
/// T <- D "+" D / D "-" D
/// D <- [0-9]+ _
/// _ <- [ \t]*
/// ```
///
/// In the example above, the rule `T` would not be a lexical rule,
/// but `D` and `_` would.  Although `D` does contain an identifier
/// to another rule, is considered to be a lexical a because the
/// identifier it contains points to a rule that is a space rule.
struct Stage1 {
    definition_names: Vec<String>,

    // stack for Identifiers that haven't had their status resolved
    unknown_ids_stk: Vec<Vec<String>>,

    // state for finding rules that match whitespace chars only
    rule_is_space: HashMap<String, Option<bool>>,
    unknown_space_ids: HashMap<String, Vec<String>>,

    // state for finding lexical rules
    rule_is_lexical: HashMap<String, Option<bool>>,
    unknown_lexical_ids: HashMap<String, Vec<String>>,

    // state for eatToken
    lexical_tokens: Vec<AST>,
}

impl Stage1 {
    fn new_with_space_rules(space_rules: Vec<String>) -> Self {
        let mut rule_is_space = HashMap::new();

        for s in &space_rules {
            rule_is_space.insert(s.clone(), Some(true));
        }

        Self {
            definition_names: vec![],
            unknown_ids_stk: vec![],
            rule_is_space,
            unknown_space_ids: HashMap::new(),
            rule_is_lexical: HashMap::new(),
            unknown_lexical_ids: HashMap::new(),
            lexical_tokens: vec![],
        }
    }

    fn is_space_rule(&self, name: &String) -> bool {
        match self.rule_is_space.get(name) {
            Some(Some(true)) => self.definition_names.contains(name),
            _ => false,
        }
    }

    fn is_lex_rule(&self, name: &str) -> bool {
        match self.rule_is_lexical.get(name) {
            Some(Some(is_space)) => *is_space,
            _ => false,
        }
    }

    fn run(&mut self, node: &AST) {
        self.traverse(node);
    }

    fn traverse(
        &mut self,
        node: &AST,
    ) -> (
        Option<bool>, /* is_space */
        Option<bool>, /* is_lex */
    ) {
        match node {
            // doesn't matter
            AST::LabelDefinition(..) => (None, None),
            // not spaces
            AST::Any | AST::Empty => (None, Some(true)),
            // identifiers are a special case for space rules
            AST::Identifier(id) => match self.rule_is_space.get(id) {
                // if it's a known identifier that points to a space rule, that implies
                // that it's a lexical rule too
                Some(Some(true)) => (Some(true), Some(true)),
                // if it's known to not point to a space rule, also forward the space status
                Some(Some(false)) => (Some(false), Some(false)),
                // otherwise, add the identifier to the ones that must be checked later
                Some(None) | None => {
                    self.unknown_ids_stk.last_mut().unwrap().push(id.clone());
                    (None, None)
                }
            },
            // forwards
            AST::Not(e) => self.traverse(e),
            AST::Label(_, e) => self.traverse(e),
            AST::Optional(e) | AST::ZeroOrMore(e) | AST::OneOrMore(e) => self.traverse(e),
            // specialized
            AST::Grammar(ev) => {
                ev.into_iter().for_each(|e| {
                    self.traverse(e);
                });

                // Find all symbols that are themselves rules with only spaces
                loop {
                    let mut has_change = false;

                    // find definitions that are still worth looking into
                    let mut maybe_rules = self.rule_is_space.clone();
                    maybe_rules.retain(|_, v| *v == None);

                    for rule in maybe_rules.keys() {
                        // if all the unknown IDs were already resolved and it has been resolved
                        // into a space rule, then we mark the `rule` itself as a space rule.
                        if self.unknown_space_ids[rule]
                            .iter()
                            .all(|id| self.rule_is_space[id] == Some(true))
                        {
                            self.rule_is_space.insert(rule.to_string(), Some(true));
                            // knowing for sure that a rule only matches spaces, also confirms
                            // that it is a lexical rule
                            self.rule_is_lexical.insert(rule.to_string(), Some(true));
                            has_change = true;
                        }
                    }
                    if !has_change {
                        break;
                    }
                }

                loop {
                    let mut has_change = false;

                    // find all rules that we're still uncertain about
                    let mut maybe_rules = self.rule_is_lexical.clone();
                    maybe_rules.retain(|_, v| *v == None);

                    for rule in maybe_rules.keys() {
                        if self.unknown_lexical_ids[rule]
                            .iter()
                            .all(|id| self.rule_is_space[id] == Some(true))
                        {
                            self.rule_is_lexical.insert(rule.to_string(), Some(true));
                            has_change = true;
                        }
                    }
                    if !has_change {
                        break;
                    }
                }
                (Some(false), Some(false))
            }
            AST::Definition(def, expr) => {
                self.definition_names.push(def.clone());

                // collect identifiers of rules that we're unsure if they're space rules or not
                self.unknown_ids_stk.push(vec![]);
                let (is_space, mut is_lex) = self.traverse(expr);
                let unknown_identifiers = self.unknown_ids_stk.pop().unwrap_or(vec![]);

                // Don't override possibly pre-loaded names in this table
                match self.rule_is_space.get(def) {
                    None => {
                        self.rule_is_space.insert(def.clone(), is_space.clone());
                    }
                    _ => {}
                }

                match is_space {
                    Some(false) => {}
                    Some(true) => {
                        // if a rule contains only spaces, we can tell right away that it is a
                        // lexical rule.  This allows us to save some work when patching.
                        is_lex = Some(true);
                    }
                    None => {
                        self.unknown_space_ids
                            .insert(def.clone(), unknown_identifiers.clone());
                    }
                }

                self.rule_is_lexical.insert(def.clone(), is_lex.clone());
                if !is_lex.is_some() {
                    self.unknown_lexical_ids
                        .insert(def.clone(), unknown_identifiers);
                }
                (is_space, is_lex)
            }
            AST::Sequence(exprs) | AST::Choice(exprs) => {
                let (mut all_spaces, mut all_lex) = (Some(true), Some(true));
                for expr in exprs {
                    let (is_space, is_lex) = self.traverse(expr);
                    all_spaces = match (is_space, all_spaces) {
                        (Some(true), Some(true)) => Some(true),
                        (Some(true) | None, Some(true) | None) => None,
                        _ => Some(false),
                    };
                    all_lex = match (is_lex, all_lex) {
                        (Some(true), Some(true)) => Some(true),
                        (Some(false), Some(false)) => Some(false),
                        (None, _) | (_, None) => None,
                        (Some(true), Some(false)) | (Some(false), Some(true)) => Some(true),
                    };
                }
                (all_spaces, all_lex)
            }
            AST::Range(a, b) => {
                self.lexical_tokens.push(AST::Range(*a, *b));
                let is_space = if char::is_whitespace(*a) && char::is_whitespace(*b) {
                    Some(true)
                } else {
                    Some(false)
                };
                (is_space, Some(true))
            }
            AST::Str(st) => {
                self.lexical_tokens.push(AST::Str(st.clone()));
                let is_space = if st.chars().all(|s| char::is_whitespace(s)) {
                    Some(true)
                } else {
                    Some(false)
                };
                (is_space, Some(true))
            }
            AST::Char(c) => {
                self.lexical_tokens.push(AST::Char(*c));
                let is_space = if char::is_whitespace(*c) {
                    Some(true)
                } else {
                    Some(false)
                };
                (is_space, Some(true))
            }
        }
    }
}

/// Taken from: On the relation between context-free grammars and
/// parsing expression grammars
///
///   FIRST(p) = { a ∈ T | G[p] axy -> y } ∪ nullable(p)
///   nullable(p) = {ε} if G[p] x -> x else ∅
///
///   FOLLOW(A) = { a ∈ T ∪ {$} | G[A] yaz -> az is in a proof tree for G w$ -> $ }
///
/// For an expression to be considered LL(1), it needs to follow
/// these two rules:
///
///   1. FIRST(p1) ∩ FIRST(p2) = ∅;
///   2. FIRST(p1) ∩ FOLLOW(A) = ∅ if ε ∈ FIRST(p2).
///
/// This is very important because conservative generation of labels
/// is only guaranteed to work with LL(1) grammars the way it is right
/// now.
fn first(node: AST) -> Vec<AST> {
    let mut first_items = if nullable(&node) {
        vec![AST::Empty]
    } else {
        vec![]
    };
    first_items.append(
        &mut match node {
            AST::Choice(items) => {
                if items.is_empty() {
                    return vec![];
                }
                items.into_iter().map(first).flatten().collect::<Vec<AST>>()
            }
            AST::Sequence(items) => {
                if items.is_empty() {
                    vec![]
                } else {
                    vec![items[0].clone()]
                }
            }
            AST::Identifier(id) => {
                vec![]
            }
            _ => vec![node],
        }
        .clone(),
    );

    first_items
}

fn nullable(node: &AST) -> bool {
    match node {
        AST::Empty | AST::Not(..) | AST::Optional(..) | AST::ZeroOrMore(..) => true,
        AST::OneOrMore(..) | AST::Any | AST::Str(..) | AST::Char(..) | AST::Range(..) => false,
        AST::Sequence(items) => items.iter().all(nullable),
        AST::Choice(items) => items.iter().any(nullable),
        AST::Identifier(id) => false,
        n => {
            panic!("Cannot tell if node is nullable: {:?}", n);
        }
    }
}

fn defs(node: &AST) -> (HashMap<String, AST>, String) {
    let mut map: HashMap<String, AST> = HashMap::new();
    let mut first_rule = "".to_string();
    let mut found_first = false;

    if let AST::Grammar(rules) = node {
        for rule in rules {
            if let AST::Definition(name, def) = rule {
                if !found_first {
                    first_rule = name.to_string();
                    found_first = true;
                }
                map.insert(name.to_string(), (**def).clone());
            }
        }
    }

    (map, first_rule)
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
    // closure.
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
mod stage1_tests {
    use super::*;

    #[test]
    fn a02() {
        env_logger::init();
        let grammar_text = "
             A <- B C       # is_space: false, is_lex: false
             B <- 'a'       # is_space: false, is_lex: true
             C <- 'b'       # is_space: false, is_lex: true
             D <- ' '       # is_space: true; literal space
             E <- '\t'      # is_space: true; escaped tab
             F <- '\n'      # is_space: true; escaped new line
             G <- '\r'      # is_space: true; escaped carriage return
             H <- ' ' G     # is_space: true; identifier points to a space rule
             I <- ' ' '\t'  # is_space: true; sequence made only of literal spaces
             J <- '\n'      # is_space: true; all options are literal space chars
                / '\r\n'
                / '\r'
             K <- J+
            ";
        let grammar = Parser::new(grammar_text).parse_grammar().unwrap();

        let (map, _) = defs(&grammar);

        println!("WATAFUK {:#?}", first(map["K"].clone()));

        // let mut stage1 = Stage1::new_with_space_rules(vec![]);
        // stage1.run(&grammar);
    }

    #[test]
    fn a01() {
        let grammar_text = "
             A <- B C       # is_space: false, is_lex: false
             B <- 'a'       # is_space: false, is_lex: true
             C <- 'b'       # is_space: false, is_lex: true
             D <- ' '       # is_space: true; literal space
             E <- '\t'      # is_space: true; escaped tab
             F <- '\n'      # is_space: true; escaped new line
             G <- '\r'      # is_space: true; escaped carriage return
             H <- ' ' G     # is_space: true; identifier points to a space rule
             I <- ' ' '\t'  # is_space: true; sequence made only of literal spaces
             J <- '\n'      # is_space: true; all options are literal space chars
                / '\r\n'
                / '\r'
            ";
        let grammar = Parser::new(grammar_text).parse_grammar().unwrap();

        let mut stage1 = Stage1::new_with_space_rules(vec![]);
        stage1.run(&grammar);

        let mut lexical_rules = stage1
            .rule_is_lexical
            .iter()
            .filter_map(|(k, v)| if *v == Some(true) { Some(k) } else { None })
            .collect::<Vec<_>>();
        lexical_rules.sort_unstable();

        assert_eq!(
            ["B", "C", "D", "E", "F", "G", "H", "I", "J"]
                .iter()
                .map(|i| i.to_owned())
                .collect::<Vec<_>>(),
            lexical_rules
        );

        let mut space_rules = stage1
            .rule_is_space
            .iter()
            .filter_map(|(k, v)| if *v == Some(true) { Some(k) } else { None })
            .collect::<Vec<_>>();
        space_rules.sort_unstable();

        assert_eq!(
            ["D", "E", "F", "G", "H", "I", "J"]
                .iter()
                .map(|i| i.to_owned())
                .collect::<Vec<_>>(),
            space_rules
        );
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
    fn follows_arith_01() {
        let mut c = Compiler::default();
        let out = c.compile_str(
            "
            assign  <- name eq expr^exas sm
            expr    <- op expr cl
                     / decimal expl
            expl    <- '*' expr^ex
                     / '/' expr^ex
                     / '+' expr^ex
                     / '-' expr^ex
                     / # Empty needed here

            decimal <- [0-9]+ _
            name    <- [a-zA-Z_][a-zA-Z0-9_]* _
            eq      <- '=' _
            sm      <- ';' _
            op      <- '(' _
            cl      <- ')' _

            _       <- ws*
            ws      <- eol / sp
            sp      <- [ \t]
            eol     <- '\n' / '\r\n' / '\r'
            ",
        );
        assert!(out.is_ok());
        let p = c.program();
        println!("{}", p);
        let mut v = vm::VM::new(p);

        // test cases

        // - label=exas,follows=["(", "[0-9]"],reason=missing expr
        //   `blah = `

        // - label=,follows=[";"],reason=missing semicolon
        //   `blah = 0`

        // - label=,follows=[],reason=
        // - label=,follows=[],reason=
        // - label=,follows=[],reason=
        // - label=,follows=[],reason=

        let result = v.run("foo = 0;");
        println!("REZULLLTZ: {:#?}", result);
    }

    #[test]
    fn follows_arith_02_lr() {
        let mut c = Compiler::default();
        let out = c.compile_str(
            "
            assign  <- name eq expr sm
            expr    <- expr:1 '+' expr:2
                     / expr:1 '-' expr:2
                     / expr:2 '*' expr:3
                     / expr:2 '/' expr:3
                     / expr:3 '**' expr:3
                     / '-' expr:4
                     / op expr:1 clk
                     / decimal

            decimal <- [0-9]+ _
            name    <- [a-zA-Z_][a-zA-Z0-9_]* _
            eq      <- '=' _
            sm      <- ';' _
            op      <- '(' _
            cl      <- ')' _
            _       <- [ \t\n\r]*
            ",
        );
        assert!(out.is_ok());
        let p = c.program();
        println!("{}", p);
        let mut v = vm::VM::new(p);
        let result = v.run("a = 3+");
        println!("REZULLLTZ: {:#?}", result);
    }

    #[test]
    fn follows_1() {
        let mut c = Compiler::default();
        let out = c.compile_str(
            "
            A <- 'a'
            B <- 'b' 'k' 'l'
            C <- ('m' / 'n') 'o'
            TerminalAfterIdentifier    <- A ';'
            ChoiceAfterIdentifier      <- A ('a' 'x' / 'b' 'y' / 'c' 'z')
            IdentifierAfterIdentifier  <- A B ('k' / 'l')
            IdChoiceAfterIdentifier    <- A C ('k' / 'l')
            EOFAfterId                 <- A !.
            ForwardIdentifier          <- A After
            After                      <- '1' / '2'
            ",
        );

        // This should be how the First sets look for the above
        // grammar:
        //
        //     First(A) = {'JustATerminal'}
        //     First(B) = {'b'}
        //     First(C) = {'m' 'n'}
        //     First(TerminalAfterIdentifier)              = First(A)
        //     First(ChoiceAfterIdentifier)                = First(A)
        //        First(ChoiceAfterIdentifier + A)         = {'a' 'b' 'c'}
        //     First(IdentifierAfterIdentifier)            = First(A)
        //        First(IdentifierAfterIdentifier + A + B) = {'k' 'l'}
        //     First(IdChoiceAfterIdentifier)              = First(A)
        //        First(IdChoiceAfterIdentifier + A)       = First(C)
        //        First(IdChoiceAfterIdentifier + A + C)   = {'k' 'l'}
        //     First(ForwardIdentifier)                    = First(A)
        //        First(ForwardIdentifier + A)             = First(After)
        //     First(After) = {'1' '2'}
        //
        // These asserts are looking at the follow set for the call
        // site of the production A within productions `*Identifier`

        assert!(out.is_ok());
        let fns: HashMap<String, usize> = c
            .funcs
            .iter()
            .map(|(k, v)| (c.strings[*k].clone(), v.addr + 2)) // 2 for call+capture
            .collect();
        let p = c.program();

        assert_eq!(
            vec![";".to_string()],
            p.expected(fns["TerminalAfterIdentifier"])
        );
        assert_eq!(
            vec!["a".to_string(), "b".to_string(), "c".to_string()],
            p.expected(fns["ChoiceAfterIdentifier"])
        );
        assert_eq!(
            vec!["b".to_string()],
            p.expected(fns["IdentifierAfterIdentifier"])
        );
        assert_eq!(
            vec!["m".to_string(), "n".to_string()],
            p.expected(fns["IdChoiceAfterIdentifier"])
        );
        assert_eq!(
            vec!["1".to_string(), "2".to_string()],
            p.expected(fns["ForwardIdentifier"])
        );
    }

    #[test]
    fn follows_2() {
        let mut c = Compiler::default();
        let out = c.compile_str(
            "
            A <- B / C
            B <- 'b' / C
            C <- 'c'
            IDAfterIDWithChoiceWithIDs <- A A
            ",
        );

        assert!(out.is_ok());
        let fns: HashMap<String, usize> = c
            .funcs
            .iter()
            .map(|(k, v)| (c.strings[*k].clone(), v.addr + 2)) // 2 for call+capture
            .collect();
        let p = c.program();

        assert_eq!(
            vec!["b".to_string(), "c".to_string()],
            p.expected(fns["IDAfterIDWithChoiceWithIDs"])
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
