use std::collections::HashMap;
use std::str::FromStr;
use egg::*;
use crate::lean_expr::*;
use crate::analysis::*;
use crate::shift_loose::*;
use crate::subst::*;
use crate::trace::*;

struct Context<'a> {
    // A map of the binder depths for each variable (which maps to loose bound variables) 
    // as it appeared in the LHS of a given rewrite. This is necessary to correctly interpret
    // the meaning of bound variables in `shifted_subst`.
    var_depths: HashMap<Var, u64>,
    // The original RHS of a rewrite which might suffer from invalid capture. 
    // In `shifted_pat` we construct an equivalent pattern, where some variables
    // are replaced with fresh variables, which are assigned according to `shifted_subst`.
    src_pat: &'a PatternAst<LeanExpr>,
    // The (partial) pattern being constructed from `pat` by switching variables for 
    // fresh variables where necessary.
    shifted_pat: PatternAst<LeanExpr>,
    // The substitution which originally maps variables in `src_pat` to their matched
    // e-classes, and subsequently also maps the fresh variables in `shifted_pat` to 
    // their corresponding shifted e-classes.
    shifted_subst: Subst,
    // A map from nodes (or variables) appearing in `shited_pat` to their index in 
    // `shifted_pat`. This is used to avoid adding the same node/variable to the pattern
    // twice by reusing the existing index.
    shifted_pat_indices: HashMap<ENodeOrVar<LeanExpr>, Id>,
    // A cache for shifted e-classes. If a shifted e-class has already been created for a 
    // given binder depth, then its corresponding variable is cached in this map.
    cache: HashMap<(u64, Id), Var>,
    // When a variable maps to a class that requires shifting, we use `subst` under the hood
    // to perform that shift. This may add new e-nodes to existing classes, which could cause
    // problems if they too are considered by `correct_bvar_indices`. Thus, we delay all unions
    // produced by `subst` and run them at the end of `correct_bvar_indices`.
    delayed_unions: Unions
}

// Given a pattern and a substitution, returns an extended substitution and adjusted pattern, such that
// applying the substitution to the pattern yields the same result except that loose bound variable indices
// are shifted such that they keep referring to the same loose bound variables. This procedure requires a 
// map of the binder depths for each variable  (which maps to loose bound variables) in the LHS of a given 
// rewrite. This is necessary to correctly interpret the meaning of bound variables in the given `subst`.
//
// This, for example, solves invalid capture of bound variables. But it is also necessary to correctly  
// perform the following rewrite:
//   
// (lam _ (lam _ ?x) 0) 0 => (lam _ ?x) 0
// matched against
// (lam _ (lam _ (bvar 5)) 0) 0
// needs to become
// (lam _ (bvar 4)) 0
pub fn correct_bvar_indices(subst: &Subst, pat: &Pattern<LeanExpr>, var_depths: HashMap<Var, u64>, graph: &mut LeanEGraph) -> (Subst, PatternAst<LeanExpr>) {    
    let root_idx = pat.ast.as_ref().len() - 1;
    let mut ctx = Context { 
        var_depths, 
        src_pat: &pat.ast, 
        shifted_pat: Default::default(), 
        shifted_subst: subst.clone(), 
        shifted_pat_indices: HashMap::new(), 
        cache: HashMap::new(),
        delayed_unions: Default::default()
    };
    correct_bvar_indices_core(root_idx, 0, &mut ctx, graph);
    perform_unions(ctx.delayed_unions, Symbol::from("λ↕"), graph);
    (ctx.shifted_subst, ctx.shifted_pat)
}

// Traverses the given pattern while constructing an analogous one which contains fresh variables for 
// all variable occurrences which would otherwise result in invalid bound variable capture of invalid loose 
// bound variable creation. Thus, if a variable maps to an e-class which does not contain loose bvars, it 
// remains as is. Otherwise, we create a fresh variable for every occurrence of a variable at different binder 
// depths. Thus, the original substitution only grows and never overwrites existing entries.
//
// Returns the index of the current node in `shifted_pat`.
fn correct_bvar_indices_core(idx: usize, binder_depth: u64, ctx: &mut Context, graph: &mut LeanEGraph) -> Id {
    dbg_trace("", TraceGroup::BVarCorrection);
    dbg_trace(format!("idx: {}", idx), TraceGroup::BVarCorrection);
    dbg_trace(format!("binder_depth: {}", binder_depth), TraceGroup::BVarCorrection);
    dbg_trace(format!("RHS: {}", ctx.shifted_pat), TraceGroup::BVarCorrection);
    dbg_trace(format!("subst: {:?}", ctx.shifted_subst), TraceGroup::BVarCorrection);
    dbg_trace(format!("pat_node_indices: {:?}", ctx.shifted_pat_indices), TraceGroup::BVarCorrection);
    dbg_trace(format!("cache: {:?}", ctx.cache), TraceGroup::BVarCorrection);

    match &ctx.src_pat.as_ref()[idx] {
        var_node@ENodeOrVar::Var(var) => {
            dbg_trace(format!("node: {}", var), TraceGroup::BVarCorrection);
            
            let target_class = ctx.shifted_subst[*var];
            // Only call this when `target_class` is known to contain loose bound variables. Otherwise,
            // `ctx.var_depths` will not contain an entry for `var`.
            let offset = || Offset::diff(binder_depth, *ctx.var_depths.get(var).unwrap());

            if graph[target_class].data.loose_bvars.is_empty() || offset().is_zero() {
                // If the given variable maps to an expression that does not contain loose bvars,
                // or if the binder depth of that variable has not changed, then we can keep it as is. 
                // But we must add it to the `shifted_pat` if it does not appear there yet.
                if let Some(shifted_pat_idx) = ctx.shifted_pat_indices.get(var_node) {
                    dbg_trace("var is needs no capture avoidance and is already contained in new RHS", TraceGroup::BVarCorrection);
                    return *shifted_pat_idx
                } else {
                    dbg_trace("var is needs no capture avoidance and is already and is being added to the new RHS", TraceGroup::BVarCorrection);
                    let new_idx = ctx.shifted_pat.add(var_node.clone());
                    ctx.shifted_pat_indices.insert(var_node.clone(), new_idx);
                    return new_idx
                }
            } else if let Some(shifted_var) = ctx.cache.get(&(binder_depth, target_class)) {
                // If there already exists a variable `shifted_var` which maps the target class 
                // to a shifted class with the correct binder depth, then simply replace the 
                // current occurrence of `var` with that variable. Since that variable must be fresh,
                // we expect it to already appear in `shift_pat` and thus in `pat_node_indices`.
                dbg_trace("shifted version is already in cache", TraceGroup::BVarCorrection);
                return *ctx.shifted_pat_indices.get(&ENodeOrVar::Var(*shifted_var)).unwrap()
            } else {
                // If the given target has not yet been shifted, create a fresh variable, replace 
                // the current occurrence of `var` with the fresh variable, and assign the shifted
                // class in the substitution.
                let fresh_var = make_fresh_var();
                let new_idx = ctx.shifted_pat.add(ENodeOrVar::Var(fresh_var));
                ctx.shifted_pat_indices.insert(ENodeOrVar::Var(fresh_var), new_idx);
                let (sub, unions) = shift_loose_bvars_without_unions(offset(), target_class, false, graph);
                ctx.delayed_unions.extend(unions);
                dbg_trace(format!("var is being replaced by fresh var {} with shifted class {}", fresh_var, sub), TraceGroup::BVarCorrection);
                ctx.shifted_subst.insert(fresh_var, sub);
                ctx.cache.insert((binder_depth, target_class), fresh_var);
                return new_idx
            }
        },
        ENodeOrVar::ENode(e) => {
            dbg_trace(format!("node: {}", e), TraceGroup::BVarCorrection);

            let mut expr = e.clone();
            for (i, child) in expr.children_mut().iter_mut().enumerate() {
                // If `expr` is a binder, increase the binder depth for its body.
                let child_binder_depth = if e.is_binder() && i == 1 { binder_depth + 1 } else { binder_depth };
                let child_idx = usize::from(*child);
                dbg_trace(format!("\nvisiting child number {} of pattern node {}", child_idx, idx), TraceGroup::BVarCorrection);
                *child = correct_bvar_indices_core(child_idx, child_binder_depth, ctx, graph);
            }

            let expr_node = ENodeOrVar::ENode(expr);
            if let Some(shifted_pat_idx) = ctx.shifted_pat_indices.get(&expr_node) {
                return *shifted_pat_idx
            } else {
                let new_idx = ctx.shifted_pat.add(expr_node.clone());
                ctx.shifted_pat_indices.insert(expr_node, new_idx);
                return new_idx
            }
        }
    }
}

fn make_fresh_var() -> Var {
    use std::sync::atomic::*;
    static COUNTER: AtomicUsize = AtomicUsize::new(0);
    let next_idx = COUNTER.fetch_add(1, Ordering::SeqCst);
    let name = format!("?fresh{}", next_idx);
    Var::from_str(&name).unwrap()
}