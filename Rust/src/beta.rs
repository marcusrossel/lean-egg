use egg::*;
use std::collections::HashMap;
use std::cmp::Ordering;
use crate::analysis::*;
use crate::lean_expr::*;
use crate::replace_bvars::*;

struct Beta {
    body: Var,
    arg: Var
}

impl Applier<LeanExpr, LeanAnalysis> for Beta {

    fn apply_one(&self, egraph: &mut LeanEGraph, beta_class: Id, subst: &Subst, _: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        let body_class = subst[self.body];
        let arg_class = subst[self.arg];
        let substituted_body_class = replace_loose_bvars(&subst_bvar_0(arg_class, rule), body_class, egraph, rule, &mut HashMap::new());
        if egraph.union_trusted(beta_class, substituted_body_class, rule) {
            vec![beta_class]
        } else {
            vec![]
        }
    }
}

fn subst_bvar_0(arg_class: Id, rule: Symbol) -> impl Fn(u64, u64, &mut LeanEGraph, &mut HashMap<u64, Id>) -> Replacement {
    move |idx, binder_depth, egraph, ctx| {
        match idx.cmp(&binder_depth) {
            Ordering::Greater => Replacement::Node(LeanExpr::BVar(egraph.add(LeanExpr::Nat(idx - 1)))),
            Ordering::Equal => {
                if let Some(class) = ctx.get(&idx) { return Replacement::Class(*class) }
                let class = replace_loose_bvars(&shift_up(binder_depth), arg_class, egraph, rule, &mut ());
                ctx.insert(idx, class);
                Replacement::Class(class)
            },
            Ordering::Less => unreachable!() // `replace_loose_bvars` provides the invariant that `idx >= binder_depth`.
        }
    }
}

fn shift_up(offset: u64) -> impl Fn(u64, u64, &mut LeanEGraph, &mut ()) -> Replacement {
    move |idx, binder_depth, egraph, _| {
        if idx < binder_depth { unreachable!() } // `replace_loose_bvars` provides the invariant that `idx >= binder_depth`. 
        Replacement::Node(LeanExpr::BVar(egraph.add(LeanExpr::Nat(idx + offset))))
    }
}

pub fn beta_reduction_rw() -> LeanRewrite {
    rewrite!("≡β"; "(app (λ ?t ?b) ?a)" => { Beta { body : "?b".parse().unwrap(), arg : "?a".parse().unwrap() }})
}
