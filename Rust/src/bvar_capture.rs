use std::collections::HashMap;
use egg::*;
use crate::lean_expr::*;
use crate::analysis::*;
use crate::replace_bvars::*;

pub struct AvoidBVarCapture {
    pub rhs: Pattern<LeanExpr>
}

impl Applier<LeanExpr, LeanAnalysis> for AvoidBVarCapture {

    fn apply_one(&self, egraph: &mut LeanEGraph, searcher_class: Id, subst: &Subst, searcher_ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        // If the matched variables do not contain loose bvars, then we can just perform the normal rewrite procedure.
        if self.rhs.vars().iter().all(|var| egraph[subst[*var]].data.loose_bvars.is_empty()) {
            // Following https://docs.rs/egg/latest/src/egg/pattern.rs.html#373
            let (from, did_something) = egraph.union_instantiations(searcher_ast.unwrap(), &self.rhs.ast, subst, rule);
            if did_something { vec![from] } else { vec![] }
        } else {
            let shifted_rhs = apply_subst_to_pat_with_shift(&self.rhs, subst, egraph);
            if egraph.union_trusted(searcher_class, shifted_rhs, rule) {
                vec![searcher_class]
            } else {
                vec![]
            }
        }
    }
}

// Following https://docs.rs/egg/latest/src/egg/language.rs.html#470
fn apply_subst_to_pat_with_shift(pat: &Pattern<LeanExpr>, subst: &Subst, egraph: &mut LeanEGraph) -> Id {
    let last = pat.ast.as_ref().len() - 1;
    apply_subst_to_pat_with_shift_aux(last, 0, pat, subst, egraph, &mut HashMap::new())
}

// TODO: For proper handling of explanations cf. https://docs.rs/egg/latest/src/egg/egraph.rs.html#590
fn apply_subst_to_pat_with_shift_aux(idx: usize, binder_depth: u64, pat: &Pattern<LeanExpr>, subst: &Subst, egraph: &mut LeanEGraph, cache: &mut HashMap<(u64, Id), Id>) -> Id {
    match &pat.ast.as_ref()[idx] {
        ENodeOrVar::Var(var) => {
            let target = subst[*var];
            if let Some(sub) = cache.get(&(binder_depth, target)) {
                *sub
            } else {
                let sub = replace_loose_bvars(&shift_up(binder_depth), target, egraph, Symbol::from("λ↕"), &mut ());
                cache.insert((binder_depth, target), sub);
                sub
            }
        },
        ENodeOrVar::ENode(e) => {
            let mut expr = e.clone();
            for (i, child) in expr.children_mut().iter_mut().enumerate() {
                // If `e` is a binder, increase the binder depth for its body.
                let child_binder_depth = if is_binder(&e) && i == 1 { binder_depth + 1 } else { binder_depth };
                let child_idx = usize::from(*child);
                *child = apply_subst_to_pat_with_shift_aux(child_idx, child_binder_depth, pat, subst, egraph, cache);
            }
            egraph.add(expr)
        }
    }
}