use slotted_egraphs::*;
use crate::lean_expr::*;

#[derive(Default, Clone, PartialEq, Eq)]
pub struct LeanAnalysis {
    pub nat_val: Option<u64>,
    pub is_primitive: bool // A class is primitive if it represents a `Nat`, `Str` or universe level e-node.
    // TODO: pub dir_val: Option<bool>,
}

impl Analysis<LeanExpr> for LeanAnalysis {

    fn merge(l: Self, r: Self) -> Self {       
        Self {
            nat_val: l.nat_val.max(r.nat_val),
            is_primitive: l.is_primitive || r.is_primitive
        }
    }

    fn make(_: &EGraph<LeanExpr, Self>, enode: &LeanExpr) -> Self {      
        match enode {
            LeanExpr::Nat(n) => Self { nat_val: Some(*n), is_primitive: true },
            
            LeanExpr::Str(_) | LeanExpr::UVar(_) | LeanExpr::Param(_) | LeanExpr::Succ(_) | 
            LeanExpr::Max(_, _) | LeanExpr::IMax(_, _) => 
                Self { is_primitive: true, ..Default::default() },

            /* TODO:

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

            LeanExpr::Fun(_) => 
                Self::Data { 
                    is_primitive: true,
                    ..Default::default() 
                },

            LeanExpr::Subst([idx, to, e]) => {
                let mut loose_bvars = egraph[*e].data.loose_bvars.clone();
                loose_bvars.remove(&egraph[*idx].data.nat_val.unwrap());
                loose_bvars.extend(&egraph[*to].data.loose_bvars);
                Self::Data { loose_bvars, ..Default::default() }
            },
            
            LeanExpr::Shift([dir, off, cut, e]) => {
                // Determine if we have a self-loop for the shift-node. If so, 
                // the shift-node must be in an e-class where some node contains 
                // no loose bvars. Thus, all other loose bvars which appear under 
                // the given e-class must be redundant. Our current handling of 
                // this situation is then to not add any shift-nodes to `e` in 
                // `shift.rs`, so we also opt to not change the set of loose bvars 
                // here. This might not be the correct approach.
                if let Some(enode_class) = egraph.lookup(enode.clone()) {
                    if egraph.find(enode_class) == egraph.find(*e) { 
                        return Self::Data { loose_bvars: egraph[*e].data.loose_bvars.clone(), ..Default::default() }
                    }
                }

                let &dir_is_up = &egraph[*dir].data.dir_val.unwrap();
                let &off = &egraph[*off].data.nat_val.unwrap();
                let &cut = &egraph[*cut].data.nat_val.unwrap();
                let mut loose_bvars: HashSet<u64> = Default::default();
                for &b in egraph[*e].data.loose_bvars.iter() {
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
            */

            _ => Default::default()
        }
    }
}

pub type LeanEGraph = EGraph<LeanExpr, LeanAnalysis>;
pub type LeanRewrite = Rewrite<LeanExpr, LeanAnalysis>;