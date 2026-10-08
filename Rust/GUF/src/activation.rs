use rs2::*;
use crate::analysis::*;
use crate::lean_expr::*;

#[derive(Default)]
pub struct Activations {
    pub nat_lit: bool,
    pub level: bool,
    pub lambda: bool,
    pub forall: bool
}

impl Activations {

    pub fn binders(&self) -> bool {
        self.lambda || self.forall
    }

    pub fn merge(&mut self, act: &Activations) {
        self.nat_lit = self.nat_lit || act.nat_lit;
        self.level   = self.level   || act.level;
        self.lambda  = self.lambda  || act.lambda;
        self.forall  = self.forall  || act.forall;
    }

    // TODO: Collect all this info in a single traversal.
    pub fn of(expr: &LeanPattern) -> Activations {
        Activations {
            nat_lit: contains_lit_or_zero(expr).is_success(),
            level: contains_max_or_imax(expr),
            lambda: contains_lambda(expr),
            forall: contains_forall(expr)
        }
    }

    pub fn report(&self) -> String {
        format!("nat-lit: {}\nlevel: {}\nlambda: {}\nforall: {}",
                self.nat_lit, self.level, self.lambda, self.forall)
    }
}

enum NatLitResult {
    Success,
    Other,
    StrNatZero,
    RawNat,
}

impl NatLitResult {
    fn is_success(&self) -> bool {
        match self {
            NatLitResult::Success => true,
            _                     => false
        }
    }
}

fn contains_lit_or_zero(expr: &LeanPattern) -> NatLitResult {
    match expr {
        Pattern::Node(e, children) => {
            match e {
                LeanExpr::Nat(_)                        => NatLitResult::RawNat,
                LeanExpr::Str(str) if str == "Nat.zero" => NatLitResult::StrNatZero,
                LeanExpr::Lit(_) => {
                    match contains_lit_or_zero(&children[0]) {
                        NatLitResult::RawNat => NatLitResult::Success,
                        _                    => NatLitResult::Other
                    }
                },
                LeanExpr::Const(ids) if ids.len() == 1 => {
                    match contains_lit_or_zero(&children[0]) {
                        NatLitResult::StrNatZero => NatLitResult::Success,
                        _                        => NatLitResult::Other
                    }
                },
                LeanExpr::App(_) | LeanExpr::Lam(_) | LeanExpr::Forall(_) | LeanExpr::Proof(_) |
                LeanExpr::Inst(_) | LeanExpr::Eq(_) | LeanExpr::Fun(_) | LeanExpr::Shaped(_) => {
                    for child in children.iter() {
                        if contains_lit_or_zero(child).is_success() {
                            return NatLitResult::Success
                        }
                    }
                    NatLitResult::Other
                },
                _ => NatLitResult::Other
            }
        },
        _ => NatLitResult::Other
    }
}

fn contains_max_or_imax(expr: &LeanPattern) -> bool {
    match expr {
        Pattern::Node(e, children) => {
            match e {
                LeanExpr::Max(_) | LeanExpr::IMax(_) => true,
                LeanExpr::Succ(_) | LeanExpr::Sort(_) | LeanExpr::Const(_) |
                LeanExpr::App(_) | LeanExpr::Lam(_) | LeanExpr::Forall(_) | LeanExpr::Proof(_) |
                LeanExpr::Inst(_) | LeanExpr::Eq(_) | LeanExpr::Fun(_) | LeanExpr::Shaped(_) => {
                    children.iter().any(contains_max_or_imax)
                },
                _ => false
            }
        },
        _ => false
    }
}

fn contains_lambda(expr: &LeanPattern) -> bool {
    match expr {
        Pattern::Node(e, children) => {
            match e {
                LeanExpr::Lam(_) => true,
                LeanExpr::App(_) | LeanExpr::Forall(_) | LeanExpr::Proof(_) | LeanExpr::Inst(_) |
                LeanExpr::Eq(_) | LeanExpr::Fun(_) | LeanExpr::Shaped(_) => {
                    children.iter().any(contains_lambda)
                },
                _ => false
            }
        },
        _ => false
    }
}

fn contains_forall(expr: &LeanPattern) -> bool {
    match expr {
        Pattern::Node(e, children) => {
            match e {
                LeanExpr::Forall(_) => true,
                LeanExpr::App(_) | LeanExpr::Lam(_) | LeanExpr::Proof(_) | LeanExpr::Inst(_) |
                LeanExpr::Eq(_) | LeanExpr::Fun(_) | LeanExpr::Shaped(_) => {
                    children.iter().any(contains_forall)
                },
                _ => false
            }
        },
        _ => false
    }
}
