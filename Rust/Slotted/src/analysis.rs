use slotted_egraphs::*;
use crate::lean_expr::*;

#[derive(Default, Clone, PartialEq, Eq)]
pub struct LeanAnalysis {
    pub nat_val: Option<u64>,
    pub is_primitive: bool // A class is primitive if it represents a `Nat`, `Str` or universe level e-node.
}

impl Analysis<LeanExpr> for LeanAnalysis {

    fn merge(l: Self, r: Self) -> Self {       
        Self {
            nat_val: l.nat_val.max(r.nat_val),
            is_primitive: l.is_primitive && r.is_primitive
        }
    }

    fn make(_: &EGraph<LeanExpr, Self>, enode: &LeanExpr) -> Self {      
        match enode {
            LeanExpr::Nat(n) => Self { nat_val: Some(*n), is_primitive: true },
            
            LeanExpr::Str(_) | LeanExpr::UVar(_) | LeanExpr::Param(_) | LeanExpr::Succ(_) | 
            LeanExpr::Max(_, _) | LeanExpr::IMax(_, _) | LeanExpr::Unknown => 
                Self { is_primitive: true, ..Default::default() },

            _ => Default::default()
        }
    }
}

pub type LeanEGraph = EGraph<LeanExpr, LeanAnalysis>;
pub type LeanRewrite = Rewrite<LeanExpr, LeanAnalysis>;