use egg::*;
use crate::lean_expr::*;

pub fn activates_nat_lit(expr: &PatternAst<LeanExpr>) -> bool {
    let root_idx = expr.as_ref().len() - 1;
    contains_lit_or_zero(expr.as_ref(), root_idx).is_success()
}

enum Result {
    StrNatZero,
    RawNat,
    Success,
    Other
}

impl Result {
    
    fn is_success(&self) -> bool {
        match self {
            Result::Success => true,
            _               => false
        }
    }

    fn merge(&mut self, res: &Result) {
        if self.is_success() || res.is_success() {
            *self = Result::Success
        } else {
            *self = Result::Other
        }
    }
}

fn contains_lit_or_zero(expr: &[ENodeOrVar<LeanExpr>], idx: usize) -> Result {
    match &expr[idx] {
        ENodeOrVar::Var(_) => { Result::Other },
        ENodeOrVar::ENode(e) => {
            match e {
                LeanExpr::Nat(_)                        => Result::RawNat,
                LeanExpr::Str(str) if str == "Nat.zero" => Result::StrNatZero,
                LeanExpr::Lit(l) => {
                    let child_idx = usize::from(*l);
                    match contains_lit_or_zero(expr, child_idx) {
                        Result::RawNat => Result::Success,
                        _              => Result::Other
                    }
                },
                LeanExpr::Const(ids) if ids.len() == 1 => {
                    let child_idx = usize::from(*ids.first().unwrap());
                    match contains_lit_or_zero(expr, child_idx) {
                        Result::StrNatZero => Result::Success,
                        _                  => Result::Other
                    }
                },
                LeanExpr::App(_) | LeanExpr::Lam(_) | LeanExpr::Forall(_) | LeanExpr::Proof(_) | 
                LeanExpr::Inst(_) | LeanExpr::Eq(_) | LeanExpr::Fun(_) | LeanExpr::Shaped(_) => {
                    let mut result = Result::Other;
                    for child in e.children().iter() {
                        let child_idx = usize::from(*child);
                        result.merge(&contains_lit_or_zero(expr, child_idx));
                    }
                    result
                },
                _ => Result::Other
            }
        }
    }
}