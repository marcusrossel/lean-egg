use std::collections::HashMap;
use egg::*;
use crate::lean_expr::*;
use crate::analysis::*;
use crate::replace_bvars::*;

pub struct BVarCapture {
    pub rhs: Pattern<LeanExpr>,
    pub block_invalid_matches: bool,
    pub shift_captured_bvars: bool
}

impl Applier<LeanExpr, LeanAnalysis> for BVarCapture {

    fn apply_one(&self, egraph: &mut LeanEGraph, _: Id, subst: &Subst, searcher_ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        let searcher_ast = searcher_ast.unwrap();
        
        // TODO: Is this cached once it is called?
        // A substitution is safe if it does not map any variables to e-classes containing loose bvars.
        let subst_is_safe = { |_ : ()| 
            self.rhs.vars().iter().all(|var| egraph[subst[*var]].data.loose_bvars.is_empty()) 
        };
        
        // Abort the rewrite if invalid matches are disallowed and the given match is invalid.
        if self.block_invalid_matches && !subst_is_safe(()) && !match_is_valid(subst, searcher_ast, egraph) {
            return vec![]
        }

        if self.shift_captured_bvars && !subst_is_safe(()) {
            let (shifted_subst, shifted_rhs) = shifted_subst_for_pat(subst, &self.rhs, egraph);
            let (from, did_union) = egraph.union_instantiations(searcher_ast, &shifted_rhs.ast, &shifted_subst, rule);
            if did_union { vec![from] } else { vec![] }
        } else {
            // Following https://docs.rs/egg/latest/src/egg/pattern.rs.html#373
            let (from, did_union) = egraph.union_instantiations(searcher_ast, &self.rhs.ast, subst, rule);
            if did_union { vec![from] } else { vec![] }
        }
    }
}

// A match (a substitution and pattern) is valid, if for each variable v in the substitution 
// which maps to an e-class with loose bvars, v only appears under the same binder.
//
// Example of an invalid match: 
// Pattern term `(lam _ (lam _, ?x) ?x)` matching against `(lam _ (lam _, (bvar 0)) (bvar 0))`.
fn match_is_valid(subst: &Subst, pat: &PatternAst<LeanExpr>, egraph: &LeanEGraph) -> bool {
    let last = pat.as_ref().len() - 1;
    match_is_valid_aux(last, vec![], None, subst, pat, egraph, &mut HashMap::new())
}

type ExprPos = Vec<usize>; 
// A binder position of `None` indicates that the associated value does not appear under a binder.
type BinderPos = Option<ExprPos>;

fn match_is_valid_aux(idx: usize, pos: ExprPos, parent_binder: BinderPos, subst: &Subst, pat: &PatternAst<LeanExpr>, egraph: &LeanEGraph, parent_binders: &mut HashMap<Var, BinderPos>) -> bool {
    match &pat.as_ref()[idx] {
        ENodeOrVar::Var(var) => {
            if egraph[subst[*var]].data.loose_bvars.is_empty() { 
                // If the given variable does not map to an e-class containing loose bvars, if cannot cause any problems.
                true 
            } else if let Some(required_parent) = parent_binders.get(var) {
                // If the given variable has already occured elsewhere in the pattern, the parent binder of that occurrence 
                // must be the same as the current parent binder.
                parent_binder == *required_parent
            } else {
                // If the given variable has not been visited yet, record its parent binder.
                parent_binders.insert(*var, parent_binder);
                true
            }
        },
        ENodeOrVar::ENode(e) => {
            for (i, child) in e.children().iter().enumerate() {
                // If `e` is a binder, set the `parent_binder` its body.
                let child_parent_binder = if is_binder(&e) && i == 1 { Some(pos.clone()) } else { parent_binder.clone() };
                let child_idx = usize::from(*child);
                let mut child_pos = pos.clone(); 
                child_pos.push(i);
                if !match_is_valid_aux(child_idx, child_pos, child_parent_binder, subst, pat, egraph, parent_binders) {
                    return false
                }
            }
            true
        }
    }
}

fn shifted_subst_for_pat(subst: &Subst, pat: &Pattern<LeanExpr>, egraph: &mut LeanEGraph) -> (Subst, Pattern<LeanExpr>) {
    let last = pat.ast.as_ref().len() - 1;
    let mut shifted_pat = pat.clone();
    let mut shifted_subst = subst.clone();
    shifted_subst_for_pat_aux(last, 0, &mut shifted_pat, &mut shifted_subst, &mut HashMap::new(), egraph);
    (shifted_subst, shifted_pat)
}

// If a variable maps to an e-class which does not contain loose bvars, it remains as is.
// Otherwise, we create a fresh variable for every occurrence of a variable at different binder depths.
// Thus, the original substitution only grows and never overwrites existing entries.
fn shifted_subst_for_pat_aux(idx: usize, binder_depth: u64, pat: &mut Pattern<LeanExpr>, subst: &mut Subst, cache: &mut HashMap<(u64, Id), Var>, egraph: &mut LeanEGraph) {
    match &pat.clone().ast.as_ref()[idx] {
        ENodeOrVar::Var(var) => {
            let target_class = subst[*var];
            
            if egraph[target_class].data.loose_bvars.is_empty() {
                // If the given variable maps to an expression that does not contain loose bvars,
                // then we can keep it as is.
                return
            } else if let Some(shifted_var) = cache.get(&(binder_depth, target_class)) {
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
                subst.insert(fresh_var, sub);
                cache.insert((binder_depth, target_class), fresh_var);
            }
        },
        ENodeOrVar::ENode(e) => {
            for (i, child) in e.children().iter().enumerate() {
                // If `e` is a binder, increase the binder depth for its body.
                let child_binder_depth = if is_binder(&e) && i == 1 { binder_depth + 1 } else { binder_depth };
                let child_idx = usize::from(*child);
                shifted_subst_for_pat_aux(child_idx, child_binder_depth, pat, subst, cache, egraph);
            }
        }
    }
}