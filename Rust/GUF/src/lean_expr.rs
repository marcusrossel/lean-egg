use rs2::*;
use symbolic_expressions::{encode_string, parser::parse_str, Sexp};
use crate::analysis::*;
use crate::proof::*;

// This mirrors the `LeanExpr` language of the egg backend, except that children are proof-annotated
// e-class ids (as required by GUF). In patterns, children are ignored (cf. `rs2::Pattern::Node`).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum LeanExpr {
    // Primitives:
    Nat(u64),
    Str(String),

    // Encoding of universe levels:
    // Note, we don't encode `zero` explicitly and use `Nat(0)` for that instead.
    UVar(PId),      // (Nat)
    Param(PId),     // (Str)
    Succ(PId),      // (<level>)
    Max([PId; 2]),  // (<level>, <level>)
    IMax([PId; 2]), // (<level>, <level>)

    // Encoding of expressions:
    BVar(PId),         // (Nat)
    FVar(PId),         // (Nat)
    MVar(PId),         // (Nat)
    Sort(PId),         // (<level>)
    Const(Box<[PId]>), // (Str, <level>*)
    App([PId; 2]),     // (<expr>, <expr>)
    Lam([PId; 2]),     // (<expr>, <expr>)
    Forall([PId; 2]),  // (<expr>, <expr>)
    Lit(PId),          // (Nat | Str)

    // Constructs for erasure:
    // Note that we also use these constructors to tag rewrite conditions (depending on whether
    // it's a type class or propositional condition).
    Proof(PId), // (<expr>)
    Inst(PId),  // (<expr>)

    // Construct for representing equality:
    // We use this *instead* of Lean's equality symbol `Eq` or propositional equivalence symbol
    // `Iff`. For an explanation see the egg backend.
    Eq([PId; 2]), // (<expr>, <expr>)

    // Construct for marking the e-class of facts syntactically. That is, we always expect to
    // have exactly one e-node `fact <i>` with `i` denoting the e-class of `const "True"`.
    Fact(PId),

    // Constructs for small-step substitution:
    Subst([PId; 3]), // (Nat, <expr>, <expr>)
    Shift([PId; 4]), // (Str, Nat, Nat, <expr>)

    // Constructs for shape annotations:
    // Note, we don't encode the shape of non-function types explicitly and use `Str("*")`) for that instead.
    Fun([PId; 2]),    // (<shape>, <shape>)
    Shaped([PId; 2]), // (<shape>, <expr>)

    // Construct for unknown terms (this is used for η-expansion):
    Unknown,
}

impl LeanExpr {

    pub fn is_binder(&self) -> bool {
        match self {
            LeanExpr::Lam(_) | LeanExpr::Forall(_) => true,
            _                                      => false
        }
    }

    pub fn is_leaf(&self) -> bool {
        self.children().is_empty()
    }

    pub fn children(&self) -> &[PId] {
        match self {
            LeanExpr::Nat(_) | LeanExpr::Str(_) | LeanExpr::Unknown => &[],
            LeanExpr::UVar(c) | LeanExpr::Param(c) | LeanExpr::Succ(c) | LeanExpr::BVar(c) |
            LeanExpr::FVar(c) | LeanExpr::MVar(c) | LeanExpr::Sort(c) | LeanExpr::Lit(c) |
            LeanExpr::Proof(c) | LeanExpr::Inst(c) | LeanExpr::Fact(c) => std::slice::from_ref(c),
            LeanExpr::Max(cs) | LeanExpr::IMax(cs) | LeanExpr::App(cs) | LeanExpr::Lam(cs) |
            LeanExpr::Forall(cs) | LeanExpr::Eq(cs) | LeanExpr::Fun(cs) | LeanExpr::Shaped(cs) => cs,
            LeanExpr::Subst(cs) => cs,
            LeanExpr::Shift(cs) => cs,
            LeanExpr::Const(cs) => cs,
        }
    }

    pub fn children_mut(&mut self) -> &mut [PId] {
        match self {
            LeanExpr::Nat(_) | LeanExpr::Str(_) | LeanExpr::Unknown => &mut [],
            LeanExpr::UVar(c) | LeanExpr::Param(c) | LeanExpr::Succ(c) | LeanExpr::BVar(c) |
            LeanExpr::FVar(c) | LeanExpr::MVar(c) | LeanExpr::Sort(c) | LeanExpr::Lit(c) |
            LeanExpr::Proof(c) | LeanExpr::Inst(c) | LeanExpr::Fact(c) => std::slice::from_mut(c),
            LeanExpr::Max(cs) | LeanExpr::IMax(cs) | LeanExpr::App(cs) | LeanExpr::Lam(cs) |
            LeanExpr::Forall(cs) | LeanExpr::Eq(cs) | LeanExpr::Fun(cs) | LeanExpr::Shaped(cs) => cs,
            LeanExpr::Subst(cs) => cs,
            LeanExpr::Shift(cs) => cs,
            LeanExpr::Const(cs) => cs,
        }
    }

    // Returns the e-node with all of its children set to `nil`.
    pub fn without_children(&self) -> LeanExpr {
        let mut node = self.clone();
        for child in node.children_mut() { *child = nil() }
        node
    }

    // The operator as displayed by egg's `define_language!` for the egg backend's `LeanExpr`.
    pub fn op(&self) -> String {
        match self {
            LeanExpr::Nat(n)    => n.to_string(),
            LeanExpr::Str(s)    => s.clone(),
            LeanExpr::UVar(_)   => "uvar".to_string(),
            LeanExpr::Param(_)  => "param".to_string(),
            LeanExpr::Succ(_)   => "succ".to_string(),
            LeanExpr::Max(_)    => "max".to_string(),
            LeanExpr::IMax(_)   => "imax".to_string(),
            LeanExpr::BVar(_)   => "bvar".to_string(),
            LeanExpr::FVar(_)   => "fvar".to_string(),
            LeanExpr::MVar(_)   => "mvar".to_string(),
            LeanExpr::Sort(_)   => "sort".to_string(),
            LeanExpr::Const(_)  => "const".to_string(),
            LeanExpr::App(_)    => "app".to_string(),
            LeanExpr::Lam(_)    => "λ".to_string(),
            LeanExpr::Forall(_) => "∀".to_string(),
            LeanExpr::Lit(_)    => "lit".to_string(),
            LeanExpr::Proof(_)  => "proof".to_string(),
            LeanExpr::Inst(_)   => "inst".to_string(),
            LeanExpr::Eq(_)     => "=".to_string(),
            LeanExpr::Fact(_)   => "fact".to_string(),
            LeanExpr::Subst(_)  => "↦".to_string(),
            LeanExpr::Shift(_)  => "↑".to_string(),
            LeanExpr::Fun(_)    => "→".to_string(),
            LeanExpr::Shaped(_) => "◇".to_string(),
            LeanExpr::Unknown   => "_".to_string(),
        }
    }

    // Mirrors `FromOp::from_op` as generated by egg's `define_language!` for the egg backend's
    // `LeanExpr`. In particular, variants are tried in order of declaration, so `Str` matches any
    // leaf which is not a `Nat` (which also means that `Unknown` is never produced by parsing).
    pub fn from_op(op: &str, children: Vec<PId>) -> Result<LeanExpr, String> {
        if children.is_empty() {
            return match op.parse() {
                Ok(n)  => Ok(LeanExpr::Nat(n)),
                Err(_) => Ok(LeanExpr::Str(op.to_string())),
            }
        }
        let arity = children.len();
        let node = match (op, arity) {
            ("uvar",  1) => LeanExpr::UVar(one(children)),
            ("param", 1) => LeanExpr::Param(one(children)),
            ("succ",  1) => LeanExpr::Succ(one(children)),
            ("max",   2) => LeanExpr::Max(many(children)),
            ("imax",  2) => LeanExpr::IMax(many(children)),
            ("bvar",  1) => LeanExpr::BVar(one(children)),
            ("fvar",  1) => LeanExpr::FVar(one(children)),
            ("mvar",  1) => LeanExpr::MVar(one(children)),
            ("sort",  1) => LeanExpr::Sort(one(children)),
            ("const", _) => LeanExpr::Const(children.into()),
            ("app",   2) => LeanExpr::App(many(children)),
            ("λ",     2) => LeanExpr::Lam(many(children)),
            ("∀",     2) => LeanExpr::Forall(many(children)),
            ("lit",   1) => LeanExpr::Lit(one(children)),
            ("proof", 1) => LeanExpr::Proof(one(children)),
            ("inst",  1) => LeanExpr::Inst(one(children)),
            ("=",     2) => LeanExpr::Eq(many(children)),
            ("fact",  1) => LeanExpr::Fact(one(children)),
            ("↦",     3) => LeanExpr::Subst(many(children)),
            ("↑",     4) => LeanExpr::Shift(many(children)),
            ("→",     2) => LeanExpr::Fun(many(children)),
            ("◇",     2) => LeanExpr::Shaped(many(children)),
            _            => return Err(format!("Failed to parse '{op}' with {arity} children"))
        };
        Ok(node)
    }
}

fn one(children: Vec<PId>) -> PId {
    children.into_iter().next().unwrap()
}

fn many<const N: usize>(children: Vec<PId>) -> [PId; N] {
    children.try_into().unwrap()
}

// Mirrors the s-expression format which egg uses to print `RecExpr`s, so that this backend
// communicates with Lean in the same format as the egg backend. GUF uses this for formatting
// patterns (and thus terms) with `{:?}`.
pub fn prettyprint(node: &LeanExpr, child_strings: Box<[String]>) -> String {
    let op = encode_string(&node.op());
    if node.is_leaf() {
        op
    } else {
        format!("({} {})", op, child_strings.join(" "))
    }
}

// Parses a pattern from the s-expression format used by egg (cf. egg's `PatternAst::from_str`).
pub fn parse_pattern(str: &str) -> Result<LeanPattern, String> {
    parse(str, true)
}

// Parses a term from the s-expression format used by egg (cf. egg's `RecExpr::from_str`).
pub fn parse_term(str: &str) -> Result<LeanTerm, String> {
    parse(str, false)
}

fn parse(str: &str, allow_vars: bool) -> Result<LeanPattern, String> {
    let sexp = parse_str(str.trim()).map_err(|e| e.to_string())?;
    from_sexp(&sexp, allow_vars)
}

fn from_sexp(sexp: &Sexp, allow_vars: bool) -> Result<LeanPattern, String> {
    let (op, args) = match sexp {
        Sexp::Empty       => return Err("Found empty s-expression".to_string()),
        Sexp::String(op)  => (op, &[][..]),
        Sexp::List(items) => match items.split_first() {
            Some((Sexp::String(op), args)) => (op, args),
            _                              => return Err(format!("Found invalid s-expression '{sexp}'"))
        }
    };

    if allow_vars && op.starts_with('?') && op.len() > 1 {
        return if args.is_empty() {
            Ok(Pattern::PVar(PVar::from(op.as_str())))
        } else {
            Err(format!("Found variable '{op}' in head position"))
        }
    }

    let children = args.iter().map(|arg| from_sexp(arg, allow_vars)).collect::<Result<Vec<_>, _>>()?;
    let node = LeanExpr::from_op(op, vec![nil(); children.len()])?;
    Ok(Pattern::Node(node, children.into()))
}
