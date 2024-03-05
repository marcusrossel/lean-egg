use std::collections::HashSet;
use egg::*;
use crate::lean_expr::*;
use crate::util::*;

#[derive(Debug, Default)]
pub struct LeanAnalysisData {
    pub nat_val:  Option<u64>,
    pub bvars:    HashSet<u64>, // A bvar is in this set only iff it is referenced by *some* e-node in the e-class.
    pub has_bvar: bool          // This is true iff some e-node in the subgraph of the given e-class is a `LeanExpr::BVar`.
}

#[derive(Default)]
pub struct LeanAnalysis;
impl Analysis<LeanExpr> for LeanAnalysis {
    type Data = LeanAnalysisData;

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        // `merge_max` prefers `Some` value over `None`. Note that if `to` and `from` both have nat values,
        // then they should have the *same* value as otherwise merging their e-classes indicates an invalid rewrite.
        //
        // TODO: We can't activate these assertions, because then egg can crashs from unsound rewrites 
        //       (cf. `Tests/Soundness.lean`). Is there a way to gracefully fail?
        // 
        // if let (Some(t), Some(f)) = (*to.nat_val, from.nat_val) { assert_eq!(t, f) }
        
        egg::merge_max(&mut to.nat_val, from.nat_val) | 
        union_sets(&mut to.bvars, from.bvars) |
        egg::merge_max(&mut to.has_bvar, from.has_bvar)
    }

    fn make(egraph: &EGraph<LeanExpr, Self>, enode: &LeanExpr) -> Self::Data {
        match enode {
            LeanExpr::Nat(n) => 
                Self::Data { 
                    nat_val: Some(*n), 
                    ..Default::default() 
                },
            
            LeanExpr::BVar(idx) => 
                Self::Data { 
                    bvars: match egraph[*idx].data.nat_val { 
                        Some(n) => vec![n].into_iter().collect(),
                        None    => HashSet::new()
                    }, 
                    has_bvar: true,
                    ..Default::default() 
                },
            
            LeanExpr::App([fun, arg]) => 
                Self::Data { 
                    bvars: union_clone(&egraph[*fun].data.bvars, &egraph[*arg].data.bvars), 
                    has_bvar: egraph[*fun].data.has_bvar || egraph[*arg].data.has_bvar,
                    ..Default::default() 
                },
            
            LeanExpr::Lam([ty, body]) | LeanExpr::Forall([ty, body]) =>
                Self::Data { 
                    bvars: union_clone(
                        &egraph[*ty].data.bvars, 
                        &shift_down(&egraph[*body].data.bvars)
                    ), 
                    has_bvar: egraph[*ty].data.has_bvar || egraph[*body].data.has_bvar,
                    ..Default::default() 
                },

            _ => Default::default()
        }
    }
}

pub type LeanEGraph = EGraph<LeanExpr, LeanAnalysis>;
pub type LeanRewrite = Rewrite<LeanExpr, LeanAnalysis>;