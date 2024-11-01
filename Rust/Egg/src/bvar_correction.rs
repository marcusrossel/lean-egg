use std::collections::HashMap;
use egg::*;
use crate::lean_expr::*;
use crate::analysis::*;

struct Context<'a> {
    // A map of the binder depths for each variable (which maps to loose bound variables) 
    // as it appeared in the LHS of a given rewrite. 
    var_depths: HashMap<Var, u64>,
    // The original RHS of a rewrite which might suffer from invalid capture. 
    src_pat: &'a PatternAst<LeanExpr>,
    // The (partial) pattern being constructed from `pat` by switching variables for 
    // shifted variables where necessary.
    shifted_pat: PatternAst<LeanExpr>,
    // A map from nodes (or variables) appearing in `shifted_pat` to their index in 
    // `shifted_pat`. This is used to avoid adding the same node/variable to the pattern
    // twice by reusing the existing index.
    shifted_pat_indices: HashMap<ENodeOrVar<LeanExpr>, Id>,
    // A cache for indices of shifted variables. If a shifted variable has already been created 
    // for a given offset, then its rec-expr index is cached in this map.
    cache: HashMap<(i64, Var), Id>
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
pub fn correct_bvar_indices(pat: &Pattern<LeanExpr>, var_depths: HashMap<Var, u64>, graph: &mut LeanEGraph) -> PatternAst<LeanExpr> {    
    let root_idx = pat.ast.as_ref().len() - 1;
    let mut ctx = Context { 
        var_depths, 
        src_pat: &pat.ast, 
        shifted_pat: Default::default(), 
        shifted_pat_indices: HashMap::new(), 
        cache: HashMap::new()
    };
    correct_bvar_indices_core(root_idx, 0, &mut ctx, graph);
    ctx.shifted_pat
}

// Traverses the given pattern while constructing an analogous one which adds shifting for all variables
// which would otherwise result in invalid bound variable capture of invalid loose bound variable creation. 
//
// Returns the index of the current node in `shifted_pat`.
fn correct_bvar_indices_core(idx: usize, binder_depth: u64, ctx: &mut Context, graph: &mut LeanEGraph) -> Id {
    match &ctx.src_pat.as_ref()[idx] {
        var_node@ENodeOrVar::Var(var) => {
            let offset = if let Some(var_depth) = ctx.var_depths.get(var) {
                (binder_depth as i64) - (*var_depth as i64)
            } else {
                0
            };
            
            // Note that a value of `0` indicates either an absence of loose bvars in the class of `var`, 
            // or an actual offset of `0`.
            if offset == 0 {
                // If the given variable maps to an expression that does not contain loose bvars,
                // or if the binder depth of that variable has not changed, then we can keep it as is. 
                add_node(ctx, var_node.clone())
            } else if let Some(shifted_var) = ctx.cache.get(&(offset, *var)) {
                // If there already exists a variable `shifted_var` which maps the variable 
                // to a shifted variable with the correct offset, then simply replace the 
                // current occurrence of `var` with that variable.
                return *shifted_var
            } else {
                // If the given variable has not yet been shifted for the current offset, then
                // create a new pattern with the correct shift for it.
                let dir = if offset >= 0 { LeanExpr::Str("+".to_string()) } else { LeanExpr::Str("-".to_string()) };
                let dir_idx     = add_node(ctx, ENodeOrVar::ENode(dir));
                let offset_idx  = add_node(ctx, ENodeOrVar::ENode(LeanExpr::Nat(offset.unsigned_abs())));
                let cutoff_zero = add_node(ctx, ENodeOrVar::ENode(LeanExpr::Nat(0)));
                let var_idx     = add_node(ctx, var_node.clone());
                add_node(ctx, ENodeOrVar::ENode(LeanExpr::Shift([dir_idx, offset_idx, cutoff_zero, var_idx])))
            }
        },
        ENodeOrVar::ENode(e) => {
            let mut expr = e.clone();
            for (i, child) in expr.children_mut().iter_mut().enumerate() {
                // If `expr` is a binder, increase the binder depth for its body.
                let child_binder_depth = if e.is_binder() && i == 1 { binder_depth + 1 } else { binder_depth };
                let child_idx = usize::from(*child);
                *child = correct_bvar_indices_core(child_idx, child_binder_depth, ctx, graph);
            }

            add_node(ctx, ENodeOrVar::ENode(expr))
        }
    }
}

fn add_node(ctx: &mut Context, node: ENodeOrVar<LeanExpr>) -> Id {
    if let Some(shifted_pat_idx) = ctx.shifted_pat_indices.get(&node) {
        *shifted_pat_idx
    } else {
        let idx = ctx.shifted_pat.add(node.clone());
        ctx.shifted_pat_indices.insert(node, idx);
        idx
    }
}