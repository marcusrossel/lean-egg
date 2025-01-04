use std::collections::HashSet;
use egg::*;
use crate::lean_expr::*;
use crate::util::*;

#[derive(Debug)]
pub struct LeanAnalysisData {
    pub nat_val:      Option<u64>,
    pub dir_val:      Option<bool>,
    pub loose_bvars:  HashSet<u64>, // A bvar is in this set only iff it is referenced by *some* e-node in the e-class.
    pub is_primitive: bool,         // A class is primitive if it represents a `Nat`, `Str` or universe level e-node.
    pub is_new:       bool,         // A class is new if it is not the result of any merge.
    pub eq:           bool          // This value is an implementation detail of the `modify` function below.
}

impl Default for LeanAnalysisData {
    
    fn default() -> Self { 
        LeanAnalysisData {
            nat_val: None,
            dir_val: None,
            loose_bvars: HashSet::default(),
            is_primitive: false,
            is_new: true,
            eq: false
        }
    }
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

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge { 
        let loose_bvar_m = if self.union_semantics {
            union_sets(&mut to.loose_bvars, from.loose_bvars)
        } else {
            intersect_sets(&mut to.loose_bvars, from.loose_bvars)
        };

        // A merged e-class is not new anymore.
        to.is_new = false;

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

            LeanExpr::Eq([l, r]) => 
                Self::Data { 
                    loose_bvars: union_clone(&egraph[*l].data.loose_bvars, &egraph[*r].data.loose_bvars),
                    eq: true,
                    ..Default::default()
                },

            _ => Default::default()
        }
    }

    // We use this hook to reify the equality inherent in an e-class.
    fn modify(egraph: &mut EGraph<LeanExpr, Self>, id: Id) {
        // We only reify equality for new e-classes as the existance of reified equality e-node is
        // invariant under e-class union.
        if !egraph[id].data.is_new { return }

        // If this e-class is new and contains an `=` node, then we skip adding an equality e-node 
        // for it. This is necessary in order to avoid looping on `modify` infinitely.
        // TODO: Is there some other way we can avoid looping? The current approach technically 
        //       breaks the existance of reified equality invariant for e-classes containing only 
        //       (non-fact) equality e-nodes.
        //       A hacky approach would be to have a global variable which blocks calls to `modify` 
        //       while adding reified equality nodes. 
        if egraph[id].data.eq { return }

        // We don't create equality e-nodes for primitive e-classes.
        if egraph[id].data.is_primitive { return }

        // Constructs the required equality e-node and adds it to the e-class of `True`.
        let eq_id = egraph.add(LeanExpr::Eq([id, id]));
        let true_id = egraph.add_expr(&"(const \"True\")".parse().unwrap());
        egraph.union_trusted(eq_id, true_id, "REIFY_EQ");
    }
}

pub type LeanEGraph = EGraph<LeanExpr, LeanAnalysis>;
pub type LeanRewrite = Rewrite<LeanExpr, LeanAnalysis>;
