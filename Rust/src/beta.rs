use egg::*;
use std::collections::HashMap;
use std::cmp::Ordering;
use crate::analysis::*;
use crate::lean_expr::*;
use crate::subst::*;

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
                BVarSub { class, unions: HashMap::new() }
            },
            Ordering::Equal => {
                let (class, unions) = subst_without_unions(arg_class, graph, &shift_up(binder_depth));
                BVarSub { class, unions }
            },
            Ordering::Less => unreachable!() // `subst` provides the invariant that `idx >= binder_depth`.
        }
    }
}

// TODO: This function is duplicated from `bvar_capture.rs`.
fn shift_up(offset: u64) -> impl Fn(u64, u64, &mut LeanEGraph) -> BVarSub {
    move |idx, binder_depth, graph| {
        if idx < binder_depth { unreachable!() } // `subst` provides the invariant that `idx >= binder_depth`. 
        let idx_class = graph.add(LeanExpr::Nat(idx + offset));
        let class = graph.add(LeanExpr::BVar(idx_class));
        BVarSub { class, unions: HashMap::new() }
    }
}

pub fn beta_reduction_rw() -> LeanRewrite {
    rewrite!("≡β"; "(app (λ ?t ?b) ?a)" => { Beta { body : "?b".parse().unwrap(), arg : "?a".parse().unwrap() }})
}
