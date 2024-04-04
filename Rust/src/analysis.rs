use std::collections::HashSet;
use egg::*;
use crate::lean_expr::*;
use crate::util::*;

#[derive(Debug, Default)]
pub struct LeanAnalysisData {
    pub nat_val:     Option<u64>,
    pub loose_bvars: HashSet<u64>, // A bvar is in this set only iff it is referenced by *some* e-node in the e-class.
}

impl LeanAnalysisData {

    // TODO: Replace `loose_bvars` with `max_loose_bvar` if eta doesn't require more precision.
    pub fn max_loose_bvar(&self) -> Option<u64> {
        self.loose_bvars.iter().max().copied()
    }
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
        union_sets(&mut to.loose_bvars, from.loose_bvars)
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
                    loose_bvars: match egraph[*idx].data.nat_val { 
                        Some(n) => vec![n].into_iter().collect(),
                        None    => HashSet::new()
                    }, 
                    ..Default::default() 
                },
            
            LeanExpr::App([fun, arg]) => 
                Self::Data { 
                    loose_bvars: union_clone(&egraph[*fun].data.loose_bvars, &egraph[*arg].data.loose_bvars),
                    ..Default::default() 
                },
            
            LeanExpr::Lam([ty, body]) | LeanExpr::Forall([ty, body]) =>
                Self::Data { 
                    loose_bvars: union_clone(
                        &egraph[*ty].data.loose_bvars, 
                        &shift_down(&egraph[*body].data.loose_bvars)
                    ), 
                    ..Default::default() 
                },

            _ => Default::default()
        }
    }
}

pub type LeanEGraph = EGraph<LeanExpr, LeanAnalysis>;
pub type LeanRewrite = Rewrite<LeanExpr, LeanAnalysis>;