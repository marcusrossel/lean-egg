use egg::*;
use std::cmp::Ordering;
use crate::analysis::*;
use crate::lean_expr::*;
use crate::subst::*;

pub enum Offset {
    Up(u64),
    Down(u64)
}

pub fn shift_loose_bvars_without_unions(offset: Offset, target_class: Id, panic_on_bvar_0: bool, graph: &mut LeanEGraph) -> (Id, Unions) {
    subst_without_unions(target_class, graph, &shift_loose_bvar(offset, panic_on_bvar_0))
}

fn shift_loose_bvar(offset: Offset, panic_on_bvar_0: bool) -> impl Fn(u64, u64, &mut LeanEGraph) -> BVarSub {
    move |idx, binder_depth, graph| {
        match (idx.cmp(&binder_depth), panic_on_bvar_0) {
            (Ordering::Greater, _) | (Ordering::Equal, false) => {
                let shifted_idx = match offset {
                    Offset::Up(o)   => idx + o,
                    Offset::Down(o) => idx - o
                };
                let idx_class = graph.add(LeanExpr::Nat(shifted_idx));
                let bvar_class = graph.add(LeanExpr::BVar(idx_class));
                BVarSub { class: bvar_class, unions: Default::default() }
            },
            (Ordering::Equal, true) => panic!(),
            // `subst` provides the invariant that `idx >= binder_depth`.
            (Ordering::Less, _) => unreachable!(), 
        }
    }
}

struct Beta {
    body: Var,
    arg: Var
}

impl Applier<LeanExpr, LeanAnalysis> for Beta {

    fn apply_one(&self, egraph: &mut LeanEGraph, beta_class: Id, s: &Subst, _: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        let body_class = s[self.body];
        let arg_class = s[self.arg];
        let substituted_body_class = subst(body_class, egraph, rule, &subst_bvar_0(arg_class));
        if egraph.union_trusted(beta_class, substituted_body_class, rule) {
            vec![beta_class]
        } else {
            vec![]
        }
    }
}

// TODO: Re-enable caching of shifted arg_classes.
fn subst_bvar_0(arg_class: Id) -> impl Fn(u64, u64, &mut LeanEGraph) -> BVarSub {
    move |idx, binder_depth, graph| {
        match idx.cmp(&binder_depth) {
            Ordering::Greater => {
                let idx_class = graph.add(LeanExpr::Nat(idx - 1));
                let class = graph.add(LeanExpr::BVar(idx_class));
                BVarSub { class, unions: Default::default() }
            },
            Ordering::Equal => {
                let (class, unions) = shift_loose_bvars_without_unions(Offset::Up(binder_depth), arg_class, false, graph);
                BVarSub { class, unions }
            },
            Ordering::Less => unreachable!() // `subst` provides the invariant that `idx >= binder_depth`.
        }
    }
}

pub fn beta_reduction_rw() -> LeanRewrite {
    rewrite!("≡β"; "(app (λ ?t ?b) ?a)" => { Beta { body : "?b".parse().unwrap(), arg : "?a".parse().unwrap() }})
}
