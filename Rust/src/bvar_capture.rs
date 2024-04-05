use std::collections::HashMap;
use std::str::FromStr;
use egg::*;
use crate::lean_expr::*;
use crate::analysis::*;
use crate::trace::*;
use crate::valid_match::*;

pub struct BVarCapture {
    pub rhs: Pattern<LeanExpr>,
    pub block_invalid_matches: bool,
    pub shift_captured_bvars: bool,
}

impl Applier<LeanExpr, LeanAnalysis> for BVarCapture {

    fn apply_one(&self, egraph: &mut LeanEGraph, _: Id, subst: &Subst, searcher_ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        let searcher_ast = searcher_ast.unwrap();
        
        // Abort the rewrite if invalid matches are disallowed and the given match is invalid.
        if self.block_invalid_matches && !match_is_valid(subst, searcher_ast, egraph) {
            return vec![]
        }

        // A substitution needs no shifting if it does not map any variables to e-classes containing loose bvars.
        let needs_no_shift = self.rhs.vars().iter().all(|var| egraph[subst[*var]].data.loose_bvars.is_empty());
        if !self.shift_captured_bvars || needs_no_shift {
            // Following https://docs.rs/egg/latest/src/egg/pattern.rs.html#373
            let (from, did_union) = egraph.union_instantiations(searcher_ast, &self.rhs.ast, subst, rule);
            if did_union { vec![from] } else { vec![] }
        } else {
            dbg_trace(format!("Start capture avoidance for\n  LHS: {}\n  RHS: {}\n  RHS Raw: {:?}\n  subst: {:?}", searcher_ast, self.rhs, self.rhs.ast.as_ref(), subst), TraceGroup::Capture);
            let (shifted_subst, shifted_rhs) = shifted_subst_for_pat(subst, &self.rhs, egraph);
            dbg_trace("End capture avoidance\n", TraceGroup::Capture);
            let (from, did_union) = egraph.union_instantiations(searcher_ast, &shifted_rhs, &shifted_subst, rule);
            if did_union { vec![from] } else { vec![] }
        }
    }
}

fn shifted_subst_for_pat(subst: &Subst, pat: &Pattern<LeanExpr>, egraph: &mut LeanEGraph) -> (Subst, PatternAst<LeanExpr>) {    
    let last = pat.ast.as_ref().len() - 1;
    let mut shifted_pat: PatternAst<LeanExpr> = Default::default();
    let mut shifted_subst = subst.clone();
    shifted_subst_for_pat_aux(last, 0, &mut shifted_pat, &mut shifted_subst, &mut HashMap::new(), &mut HashMap::new(), egraph, pat);
    (shifted_subst, shifted_pat)
}

// If a variable maps to an e-class which does not contain loose bvars, it remains as is.
// Otherwise, we create a fresh variable for every occurrence of a variable at different binder depths.
// Thus, the original substitution only grows and never overwrites existing entries.
//
// * `idx`: identifier the node in `pat` (`pat[idx]`) currently being shifted
// * `binder_depth`: the number of binders appearing above the current node
// * `shifted_pat`: the partial pattern being constructed from `pat` by adding fresh variables where necessary
// * `subst`: the shifted substitution being constructed
// * `pat_node_indices`: a map showing which nodes appear at which index in `shifted_pat`
// * `cache`: a cache showing if an existing variable already maps to a given e-class shifted by a given offset
// 
// Returns the index of the current node in `shifted_pat`.
//
// TODO: Factor out adding a node to the shifted pattern after checking if it already has a corresponding index.
fn shifted_subst_for_pat_aux(
    idx: usize, 
    binder_depth: u64, 
    shifted_pat: &mut PatternAst<LeanExpr>, 
    subst: &mut Subst, 
    pat_node_indices: &mut HashMap<ENodeOrVar<LeanExpr>, Id>, 
    cache: &mut HashMap<(u64, Id), Var>, 
    egraph: &mut LeanEGraph, 
    pat: &Pattern<LeanExpr>
) -> Id {
    dbg_trace("", TraceGroup::Capture);
    dbg_trace(format!("idx: {}", idx), TraceGroup::Capture);
    dbg_trace(format!("binder_depth: {}", binder_depth), TraceGroup::Capture);
    dbg_trace(format!("RHS: {}", shifted_pat), TraceGroup::Capture);
    dbg_trace(format!("subst: {:?}", subst), TraceGroup::Capture);
    dbg_trace(format!("pat_node_indices: {:?}", pat_node_indices), TraceGroup::Capture);
    dbg_trace(format!("cache: {:?}", cache), TraceGroup::Capture);

    match &pat.ast.as_ref()[idx] {
        var_node@ENodeOrVar::Var(var) => {
            dbg_trace(format!("node: {}", var), TraceGroup::Capture);
            
            let target_class = subst[*var];
            
            if egraph[target_class].data.loose_bvars.is_empty() {
                // If the given variable maps to an expression that does not contain loose bvars,
                // then we can keep it as is. But we must add it to the `shifted_pat` if it does 
                // not appear there yet.
                if let Some(shifted_pat_idx) = pat_node_indices.get(var_node) {
                    dbg_trace("var is needs no capture avoidance and is already contained in new RHS", TraceGroup::Capture);
                    return *shifted_pat_idx
                } else {
                    dbg_trace("var is needs no capture avoidance and is already and is being added to the new RHS", TraceGroup::Capture);
                    let new_idx = shifted_pat.add(var_node.clone());
                    pat_node_indices.insert(var_node.clone(), new_idx);
                    return new_idx
                }
            } else if let Some(shifted_var) = cache.get(&(binder_depth, target_class)) {
                // If there already exists a variable `shifted_var` which maps the target class 
                // to a shifted class with the correct binder depth, then simply replace the 
                // current occurrence of `var` with that variable. Since that variable must be fresh,
                // we expect it to already appear in `shift_pat` and thus in `pat_node_indices`.
                dbg_trace("shifted version is already in cache", TraceGroup::Capture);
                return *pat_node_indices.get(&ENodeOrVar::Var(*shifted_var)).unwrap()
            } else {
                // If the given target has not yet been shifted, create a fresh variable, replace 
                // the current occurrence of `var` with the fresh variable, and assign the shifted
                // class in the substitution.
                let fresh_var = make_fresh_var();
                let new_idx = shifted_pat.add(ENodeOrVar::Var(fresh_var));
                pat_node_indices.insert(ENodeOrVar::Var(fresh_var), new_idx);
                let sub = crate::subst::subst(target_class, egraph, Symbol::from("λ↕"), &shift_up(binder_depth));
                dbg_trace(format!("var is being replaced by fresh var {} with shifted class {}", fresh_var, sub), TraceGroup::Capture);
                subst.insert(fresh_var, sub);
                cache.insert((binder_depth, target_class), fresh_var);
                return new_idx
            }
        },
        ENodeOrVar::ENode(e) => {
            dbg_trace(format!("node: {}", e), TraceGroup::Capture);

            let mut expr = e.clone();
            for (i, child) in expr.children_mut().iter_mut().enumerate() {
                // If `expr` is a binder, increase the binder depth for its body.
                let child_binder_depth = if is_binder(&e) && i == 1 { binder_depth + 1 } else { binder_depth };
                let child_idx = usize::from(*child);
                dbg_trace(format!("\nvisiting child number {} of pattern node {}", child_idx, idx), TraceGroup::Capture);
                *child = shifted_subst_for_pat_aux(child_idx, child_binder_depth, shifted_pat, subst, pat_node_indices, cache, egraph, pat);
            }

            let expr_node = ENodeOrVar::ENode(expr);
            if let Some(shifted_pat_idx) = pat_node_indices.get(&expr_node) {
                return *shifted_pat_idx
            } else {
                let new_idx = shifted_pat.add(expr_node.clone());
                pat_node_indices.insert(expr_node, new_idx);
                return new_idx
            }
        }
    }
}

fn shift_up(offset: u64) -> impl Fn(u64, u64, &mut LeanEGraph) -> LeanExpr {
    move |idx, binder_depth, egraph| {
        if idx < binder_depth { unreachable!() } // `subst` provides the invariant that `idx >= binder_depth`. 
        LeanExpr::BVar(egraph.add(LeanExpr::Nat(idx + offset)))
    }
}

fn make_fresh_var() -> Var {
    use std::sync::atomic::*;
    static COUNTER: AtomicUsize = AtomicUsize::new(0);
    let next_idx = COUNTER.fetch_add(1, Ordering::SeqCst);
    let name = format!("?fresh-var-{}", next_idx);
    Var::from_str(&name).unwrap()
}