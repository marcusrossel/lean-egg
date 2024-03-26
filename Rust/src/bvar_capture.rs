use std::collections::HashMap;
use egg::*;
use crate::lean_expr::*;
use crate::analysis::*;
use crate::replace_bvars::*;

// TODO: We're currently not protecting against the case where the searcher contains two references to a variable `?x``
//       and this pattern is matched against expressions containing bvars where the given bvars occur under different
//       binders.
//       E.g. if we have pattern term "(lam _ (lam _, ?x) ?x)" and match it against "(lam _ (lam _, (bvar 0)) (bvar 0))".
//
//       Note: blocking this might be a problem in settings where bvars are contained in the same e-class as other enodes.
 
pub struct BVarCapture {
    pub rhs: Pattern<LeanExpr>,
    pub block_invalid_matches: bool,
    pub shift_captured_bvars: bool
    
}

impl Applier<LeanExpr, LeanAnalysis> for BVarCapture {

    fn apply_one(&self, egraph: &mut LeanEGraph, _: Id, subst: &Subst, searcher_ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        // TODO: Is this cached once it is called?
        let subst_is_safe = { |_ : ()| 
            self.rhs.vars().iter().all(|var| egraph[subst[*var]].data.loose_bvars.is_empty()) 
        };
        
        if self.block_invalid_matches && !subst_is_safe(()) {
            todo!()
        }
        
        if self.shift_captured_bvars && !subst_is_safe(()) {
            let (shifted_subst, shifted_rhs) = shifted_subst_for_pat(subst, &self.rhs, egraph);
            let (from, did_union) = egraph.union_instantiations(searcher_ast.unwrap(), &shifted_rhs.ast, &shifted_subst, rule);
            if did_union { vec![from] } else { vec![] }
        } else {
            // Following https://docs.rs/egg/latest/src/egg/pattern.rs.html#373
            let (from, did_union) = egraph.union_instantiations(searcher_ast.unwrap(), &self.rhs.ast, subst, rule);
            if did_union { vec![from] } else { vec![] }
        }
    }
}

struct DSubst {
    subst: Subst,
    cache: HashMap<(u64, Id), Var>
}

fn shifted_subst_for_pat(subst: &Subst, pat: &Pattern<LeanExpr>, egraph: &mut LeanEGraph) -> (Subst, Pattern<LeanExpr>) {
    let last = pat.ast.as_ref().len() - 1;
    let mut shifted_pat = pat.clone();
    let mut dsubst = DSubst { subst: subst.clone(), cache: HashMap::new() };
    shifted_subst_for_pat_aux(last, 0, &mut shifted_pat, &mut dsubst, egraph);
    (dsubst.subst, shifted_pat)
}

// If a variable maps to an e-class which does not contain loose bvars, it remains as is.
// Otherwise, we create a fresh variable for every occurrence of a variable at different binder depths.
// Thus, the original substitution only grows and never overwrites existing entries.
fn shifted_subst_for_pat_aux(idx: usize, binder_depth: u64, pat: &mut Pattern<LeanExpr>, dsubst: &mut DSubst, egraph: &mut LeanEGraph) {
    match &pat.clone().ast.as_ref()[idx] {
        ENodeOrVar::Var(var) => {
            let target_class = dsubst.subst[*var];
            
            if egraph[target_class].data.loose_bvars.is_empty() {
                // If the given variable maps to an expression that does not contain loose bvars,
                // then we can keep it as is.
                return
            } else if let Some(shifted_var) = dsubst.cache.get(&(binder_depth, target_class)) {
                // If there already exists a variable `shifted_var` which maps the target class 
                // to a shifted class with the correct binder depth, then simply replace the 
                // current occurrence of `var` with that variable.
                todo!(); // TODO: Replace the variable in `pat`.
            } else {
                // If the given target has not yet been shifted, create a fresh variable, replace 
                // the current occurrence of `var` with the fresh variable, and assign the shifted
                // class in the substitution.
                let &fresh_var = var; // TODO: Make a fresh variable and replace it in `pat`.
                let sub = replace_loose_bvars(&shift_up(binder_depth), target_class, egraph, Symbol::from("λ↕"), &mut ());
                dsubst.subst.insert(fresh_var, sub);
                dsubst.cache.insert((binder_depth, target_class), fresh_var);
            }
        },
        ENodeOrVar::ENode(e) => {
            for (i, child) in e.children().iter().enumerate() {
                // If `e` is a binder, increase the binder depth for its body.
                let child_binder_depth = if is_binder(&e) && i == 1 { binder_depth + 1 } else { binder_depth };
                let child_idx = usize::from(*child);
                shifted_subst_for_pat_aux(child_idx, child_binder_depth, pat, dsubst, egraph);
            }
        }
    }
}