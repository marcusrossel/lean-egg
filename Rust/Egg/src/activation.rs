use std::io::Empty;

use egg::*;
use crate::lean_expr::*;

pub fn activates_nat_lit(expr: &PatternAst<LeanExpr>) -> bool {
    let root_idx = expr.as_ref().len() - 1;
    contains_lit_or_zero(expr.as_ref(), root_idx).is_success()
}

pub fn activates_lvl(expr: &PatternAst<LeanExpr>) -> bool {
    let root_idx = expr.as_ref().len() - 1;
    contains_max_or_imax(expr.as_ref(), root_idx).is_success()
}

enum Result<S> {
    Success,
    Other,
    Subterm(S)
}

impl<S> Result<S> {
    fn is_success(&self) -> bool {
        match self {
            Result::Success => true,
            _               => false
        }
    }
}
enum NatLitSubterm {
    StrNatZero,
    RawNat
}

fn contains_lit_or_zero(expr: &[ENodeOrVar<LeanExpr>], idx: usize) -> Result<NatLitSubterm> {
    match &expr[idx] {
        ENodeOrVar::Var(_) => { Result::Other },
        ENodeOrVar::ENode(e) => {
            match e {
                LeanExpr::Nat(_)                        => Result::Subterm(NatLitSubterm::RawNat),
                LeanExpr::Str(str) if str == "Nat.zero" => Result::Subterm(NatLitSubterm::StrNatZero),
                LeanExpr::Lit(l) => {
                    let child_idx = usize::from(*l);
                    match contains_lit_or_zero(expr, child_idx) {
                        Result::Subterm(NatLitSubterm::RawNat) => Result::Success,
                        _                                      => Result::Other
                    }
                },
                LeanExpr::Const(ids) if ids.len() == 1 => {
                    let child_idx = usize::from(*ids.first().unwrap());
                    match contains_lit_or_zero(expr, child_idx) {
                        Result::Subterm(NatLitSubterm::StrNatZero) => Result::Success,
                        _                                          => Result::Other
                    }
                },
                LeanExpr::App(_) | LeanExpr::Lam(_) | LeanExpr::Forall(_) | LeanExpr::Proof(_) | 
                LeanExpr::Inst(_) | LeanExpr::Eq(_) | LeanExpr::Fun(_) | LeanExpr::Shaped(_) => {
                    for child in e.children().iter() {
                        let child_idx = usize::from(*child);
                        if contains_lit_or_zero(expr, child_idx).is_success() { 
                            return Result::Success 
                        }
                    }
                    Result::Other
                },
                _ => Result::Other
            }
        }
    }
}

fn contains_max_or_imax(expr: &[ENodeOrVar<LeanExpr>], idx: usize) -> Result<Empty> {
    match &expr[idx] {
        ENodeOrVar::Var(_) => { Result::Other },
        ENodeOrVar::ENode(e) => {
            match e {
                LeanExpr::Max(_) | LeanExpr::IMax(_) => 
                    Result::Success,
                LeanExpr::Succ(_) | LeanExpr::Sort(_) | LeanExpr::Const(_) |
                LeanExpr::App(_) | LeanExpr::Lam(_) | LeanExpr::Forall(_) | LeanExpr::Proof(_) | 
                LeanExpr::Inst(_) | LeanExpr::Eq(_) | LeanExpr::Fun(_) | LeanExpr::Shaped(_) => {
                    for child in e.children().iter() {
                        let child_idx = usize::from(*child);
                        if contains_max_or_imax(expr, child_idx).is_success() {
                            return Result::Success
                        }
                    }
                    Result::Other
                },
                _ => Result::Other
            }
        }
    }
}