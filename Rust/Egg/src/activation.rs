use egg::*;
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
    pub fn of(expr: &PatternAst<LeanExpr>) -> Activations {
        let root_idx = expr.as_ref().len() - 1;
        Activations {
            nat_lit: contains_lit_or_zero(expr.as_ref(), root_idx).is_success(),
            level: contains_max_or_imax(expr.as_ref(), root_idx),
            lambda: contains_lambda(expr.as_ref(), root_idx),
            forall: contains_forall(expr.as_ref(), root_idx)
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

fn contains_lit_or_zero(expr: &[ENodeOrVar<LeanExpr>], idx: usize) -> NatLitResult {
    match &expr[idx] {
        ENodeOrVar::Var(_) => { NatLitResult::Other },
        ENodeOrVar::ENode(e) => {
            match e {
                LeanExpr::Nat(_)                        => NatLitResult::RawNat,
                LeanExpr::Str(str) if str == "Nat.zero" => NatLitResult::StrNatZero,
                LeanExpr::Lit(l) => {
                    let child_idx = usize::from(*l);
                    match contains_lit_or_zero(expr, child_idx) {
                        NatLitResult::RawNat => NatLitResult::Success,
                        _                    => NatLitResult::Other
                    }
                },
                LeanExpr::Const(ids) if ids.len() == 1 => {
                    let child_idx = usize::from(*ids.first().unwrap());
                    match contains_lit_or_zero(expr, child_idx) {
                        NatLitResult::StrNatZero => NatLitResult::Success,
                        _                        => NatLitResult::Other
                    }
                },
                LeanExpr::App(_) | LeanExpr::Lam(_) | LeanExpr::Forall(_) | LeanExpr::Proof(_) | 
                LeanExpr::Inst(_) | LeanExpr::Eq(_) | LeanExpr::Fun(_) | LeanExpr::Shaped(_) => {
                    for child in e.children().iter() {
                        let child_idx = usize::from(*child);
                        if contains_lit_or_zero(expr, child_idx).is_success() { 
                            return NatLitResult::Success 
                        }
                    }
                    NatLitResult::Other
                },
                _ => NatLitResult::Other
            }
        }
    }
}

fn contains_max_or_imax(expr: &[ENodeOrVar<LeanExpr>], idx: usize) -> bool {
    match &expr[idx] {
        ENodeOrVar::Var(_) => { false },
        ENodeOrVar::ENode(e) => {
            match e {
                LeanExpr::Max(_) | LeanExpr::IMax(_) => true,
                LeanExpr::Succ(_) | LeanExpr::Sort(_) | LeanExpr::Const(_) |
                LeanExpr::App(_) | LeanExpr::Lam(_) | LeanExpr::Forall(_) | LeanExpr::Proof(_) | 
                LeanExpr::Inst(_) | LeanExpr::Eq(_) | LeanExpr::Fun(_) | LeanExpr::Shaped(_) => {
                    for child in e.children().iter() {
                        let child_idx = usize::from(*child);
                        if contains_max_or_imax(expr, child_idx) { return true }
                    }
                    false
                },
                _ => false
            }
        }
    }
}

fn contains_lambda(expr: &[ENodeOrVar<LeanExpr>], idx: usize) -> bool {
    match &expr[idx] {
        ENodeOrVar::Var(_) => { false },
        ENodeOrVar::ENode(e) => {
            match e {
                LeanExpr::Lam(_) => true,
                LeanExpr::App(_) | LeanExpr::Forall(_) | LeanExpr::Proof(_) | LeanExpr::Inst(_) | 
                LeanExpr::Eq(_) | LeanExpr::Fun(_) | LeanExpr::Shaped(_) => {
                    for child in e.children().iter() {
                        let child_idx = usize::from(*child);
                        if contains_lambda(expr, child_idx) { return true }
                    }
                    false
                },
                _ => false
            }
        }
    }
}

fn contains_forall(expr: &[ENodeOrVar<LeanExpr>], idx: usize) -> bool {
    match &expr[idx] {
        ENodeOrVar::Var(_) => { false },
        ENodeOrVar::ENode(e) => {
            match e {
                LeanExpr::Forall(_) => true,
                LeanExpr::App(_) | LeanExpr::Lam(_) | LeanExpr::Proof(_) | LeanExpr::Inst(_) | 
                LeanExpr::Eq(_) | LeanExpr::Fun(_) | LeanExpr::Shaped(_) => {
                    for child in e.children().iter() {
                        let child_idx = usize::from(*child);
                        if contains_forall(expr, child_idx) { return true }
                    }
                    false
                },
                _ => false
            }
        }
    }
}