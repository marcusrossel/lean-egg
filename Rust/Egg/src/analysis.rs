use std::collections::HashSet;
use egg::*;
use crate::lean_expr::*;
use crate::util::*;

#[derive(Debug, Default)]
pub struct LeanAnalysisData {
    pub nat_val:      Option<u64>,
    pub dir_val:      Option<bool>,
    pub loose_bvars:  HashSet<u64>, // A bvar is in this set only iff it is referenced by *some* e-node in the e-class.
    pub is_primitive: bool          // A class is primitive if it represents a `Nat`, `Str` or universe level e-node.
}

#[derive(Default)]
pub struct LeanAnalysis {
    pub union_semantics: bool,
}

impl LeanAnalysis { 
    pub fn loose_bvar_idx_limit() -> u64 { 100 }
}

impl Analysis<LeanExpr> for LeanAnalysis {
    type Data = LeanAnalysisData;

    // We use this hook to reify the equality inherent in an e-class.
    fn modify(egraph: &mut EGraph<LeanExpr, Self>, id: Id) {
        // WARNING: We have to be careful here to only add the equality e-node if it does not 
        //          already exist. Otherwise we loop on this function infinitely.
        
        // Heuristic: if the e-class contains more than one e-node it's not new.
        if egraph[id].len() > 1 { return }

        // We don't create equality e-nodes for primitive classes.
        if egraph[id].data.is_primitive { return }

        // Constructs the required equality e-node, but aborts if the e-graph already contains it.
        
        let eq_const: Id; 
        let eq_const_expr = "(app (const \"Eq\" _) _)".parse().unwrap();
        if let Some(e) = egraph.lookup_expr(&eq_const_expr) {
            eq_const = e;
        } else {
            eq_const = egraph.add_expr(&eq_const_expr);
        };
        
        let eq: LeanExpr;
        if let Some(eq_lhs) = egraph.lookup(LeanExpr::App([eq_const, id])) {
            eq = LeanExpr::App([eq_lhs, id]);
            if egraph.lookup(eq.clone()).is_some() { return }
        } else {
            // PROBLEM: When we add `(app eq_const id)`, this induces another call to `modify` which
            //          then tries to construct the equality e-node for `(app eq_const id)`, which 
            //          then adds `(app eq_const (app eq_const id))`, which induces another call to 
            //          `modify`, etc.
            let eq_lhs = egraph.add(LeanExpr::App([eq_const, id]));
            eq = LeanExpr::App([eq_lhs, id]);
        }
        
        let eq_id = egraph.add(eq);
        let true_id = egraph.lookup_expr(&"(const \"True\")".parse().unwrap()).unwrap();
        egraph.union_trusted(eq_id, true_id, "REIFY_EQ");
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge { 
        let loose_bvar_m = if self.union_semantics {
            union_sets(&mut to.loose_bvars, from.loose_bvars)
        } else {
            intersect_sets(&mut to.loose_bvars, from.loose_bvars)
        };

        // `merge_max` prefers `Some` value over `None`. Note that if `to` and `from` both have nat 
        // values, then they should have the *same* value as otherwise merging their e-classes 
        // indicates an invalid rewrite. The same applies for the `dir_val`s.
        egg::merge_max(&mut to.nat_val, from.nat_val) | 
        egg::merge_max(&mut to.dir_val, from.dir_val) | 
        egg::merge_max(&mut to.is_primitive, from.is_primitive) |
        loose_bvar_m
    }

    fn make(egraph: &EGraph<LeanExpr, Self>, enode: &LeanExpr) -> Self::Data {      
        match enode {
            LeanExpr::Nat(n) => 
                Self::Data { 
                    nat_val: Some(*n), 
                    is_primitive: true,
                    ..Default::default() 
                },
            
            LeanExpr::Str(shift_up) if shift_up == "+" => 
                Self::Data { 
                    dir_val: Some(true), 
                    is_primitive: true,
                    ..Default::default() 
                },
            
            LeanExpr::Str(shift_down) if shift_down == "-" => 
                Self::Data { 
                    dir_val: Some(false), 
                    is_primitive: true,
                    ..Default::default() 
                },

            LeanExpr::Str(_) | LeanExpr::Fun(_) | LeanExpr::UVar(_) | LeanExpr::Param(_) | 
            LeanExpr::Succ(_) | LeanExpr::Max(_) | LeanExpr::IMax(_) | LeanExpr::Fact(_) | 
            LeanExpr::Unknown => 
                Self::Data { 
                    is_primitive: true,
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
                    // TODO: Only do this when union semantics are active.
                    if b > Self::loose_bvar_idx_limit() { continue; }

                    if b < cut {
                        loose_bvars.insert(b);
                    } else if dir_is_up {
                        loose_bvars.insert(b + off);
                    } else if off <= b {
                        // If `off > b`, this shift was "not intended", so we just don't do it. 
                        loose_bvars.insert(b - off);
                    }
                }

                Self::Data { loose_bvars, ..Default::default() }
            },

            LeanExpr::Shaped([_, e]) | LeanExpr::Proof(e) | LeanExpr::Inst(e) =>
                Self::Data { 
                    loose_bvars: egraph[*e].data.loose_bvars.clone(), 
                    ..Default::default() 
                },

            _ => Default::default()
        }
    }
}

pub type LeanEGraph = EGraph<LeanExpr, LeanAnalysis>;
pub type LeanRewrite = Rewrite<LeanExpr, LeanAnalysis>;
