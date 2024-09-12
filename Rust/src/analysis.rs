use std::collections::HashSet;
use egg::*;
use crate::lean_expr::*;
use crate::util::*;

#[derive(Debug, Default)]
pub struct LeanAnalysisData {
    pub nat_val:     Option<u64>,
    pub dir_val:     Option<bool>,
    pub loose_bvars: HashSet<u64>, // A bvar is in this set only iff it is referenced by *some* e-node in the e-class.
}

#[derive(Default)]
pub struct LeanAnalysis;
impl Analysis<LeanExpr> for LeanAnalysis {
    type Data = LeanAnalysisData;

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {       
        // `merge_max` prefers `Some` value over `None`. Note that if `to` and `from` both have nat values,
        // then they should have the *same* value as otherwise merging their e-classes indicates an invalid 
        // rewrite. The same applies for the `dir_val`s.
        egg::merge_max(&mut to.nat_val, from.nat_val) | 
        egg::merge_max(&mut to.dir_val, from.dir_val) | 
        union_sets(&mut to.loose_bvars, from.loose_bvars)
    }

    fn make(egraph: &EGraph<LeanExpr, Self>, enode: &LeanExpr) -> Self::Data {      
        match enode {
            LeanExpr::Nat(n) => 
                Self::Data { 
                    nat_val: Some(*n), 
                    ..Default::default() 
                },
            
            LeanExpr::Str(shift_up) if shift_up == "+" => 
                Self::Data { 
                    dir_val: Some(true), 
                    ..Default::default() 
                },
            
                LeanExpr::Str(shift_down) if shift_down == "-" => 
                Self::Data { 
                    dir_val: Some(false), 
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

            LeanExpr::Subst([idx, to, e]) => {
                let mut loose_bvars = egraph[*e].data.loose_bvars.clone();
                loose_bvars.remove(&egraph[*idx].data.nat_val.unwrap());
                loose_bvars.extend(&egraph[*to].data.loose_bvars);
                Self::Data { loose_bvars, ..Default::default() }
            },
            
            LeanExpr::Shift([dir, off, cut, e]) => {
                let &dir_is_up = &egraph[*dir].data.dir_val.unwrap();
                let &off = &egraph[*off].data.nat_val.unwrap();
                let &cut = &egraph[*cut].data.nat_val.unwrap();
                let mut loose_bvars: HashSet<u64> = Default::default();
                for &b in egraph[*e].data.loose_bvars.iter() {
                    if b < cut {
                        loose_bvars.insert(b);
                    } else if dir_is_up {
                        loose_bvars.insert(b + off);
                    } else {
                        loose_bvars.insert(b.saturating_sub(off));
                    }
                }
                Self::Data { loose_bvars, ..Default::default() }
            },

            _ => Default::default()
        }
    }
}

pub type LeanEGraph = EGraph<LeanExpr, LeanAnalysis>;
pub type LeanRewrite = Rewrite<LeanExpr, LeanAnalysis>;