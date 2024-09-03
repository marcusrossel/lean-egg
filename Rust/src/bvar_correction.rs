use std::collections::HashMap;
use egg::*;
use crate::lean_expr::*;
use crate::analysis::*;

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
    // variables under substitution where necessary.
    shifted_pat: PatternAst<LeanExpr>,
    // A map from nodes (or variables) appearing in `shifted_pat` to their index in 
    // `shifted_pat`. This is used to avoid adding the same node/variable to the pattern
    // twice by reusing the existing index.
    shifted_pat_indices: HashMap<ENodeOrVar<LeanExpr>, Id>,
    // A cache for indices of shifted variables. If a shifted variable has already been created 
    // for a given offset, then its rec-expr index is cached in this map.
    cache: HashMap<(i64, Var), Id>,
    // The substitution which originally maps variables in `src_pat` to their matched e-classes.
    subst: &'a Subst
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
pub fn correct_bvar_indices(subst: &Subst, pat: &Pattern<LeanExpr>, var_depths: HashMap<Var, u64>, graph: &mut LeanEGraph) -> PatternAst<LeanExpr> {    
    let root_idx = pat.ast.as_ref().len() - 1;
    let mut ctx = Context { 
        var_depths, 
        src_pat: &pat.ast, 
        shifted_pat: Default::default(), 
        shifted_pat_indices: HashMap::new(), 
        cache: HashMap::new(),
        subst: subst
    };
    correct_bvar_indices_core(root_idx, 0, &mut ctx, graph);
    ctx.shifted_pat
}

// Traverses the given pattern while constructing an analogous one which adds substitutions for all variables
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
                // create a new pattern with the correct substitutions for it.
                add_shifted(var, offset, ctx, graph)
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

fn add_shifted(var: &Var, offset: i64, ctx: &mut Context, graph: &LeanEGraph) -> Id {
    let mut shifted = add_node(ctx, ENodeOrVar::Var(*var));

    // As substitution does not occurr "all at once", it is important that we apply the 
    // substitutions ordered from smaller to larger indices when the offset is negative
    // and larger to smaller indices when the offset is positive. Otherwise, indices might 
    // be  shifted multiple times as in `(↦ 1 0 (↦ 2 1 e))`, which ends up shifting 2 to 0, 
    // whereas `(↦ 2 1 (↦ 1 0 e))` does not.
    //
    // I guess we might still be able to run into this problem if some other rewrite introduces
    // a substitution on `e` which maps an index to `1` or `2`. The difference then is that 
    // the order of rewrites could be swapped, so the substitutions can also be applied in the
    // "correct" order. Thus, we may generate some junk in the e-graph, but we don't block any
    // successful paths. As such, I think should be able to ignore this issue if it does not 
    // cause too many problems in practice (kind of like bvar aliasing). 
    let mut sorted_bvars = graph[ctx.subst[*var]].data.loose_bvars.iter().collect::<Vec<_>>();
    sorted_bvars.sort_by(|lhs, rhs| if offset <= 0 { lhs.cmp(rhs) } else { rhs.cmp(lhs) });

    for &bvar in sorted_bvars {
        let from = add_node(ctx, ENodeOrVar::ENode(LeanExpr::Nat(bvar)));
        let to   = add_node(ctx, ENodeOrVar::ENode(LeanExpr::Nat(((bvar as i64) + offset) as u64)));
        shifted  = add_node(ctx, ENodeOrVar::ENode(LeanExpr::Subst([from, to, shifted])));
    }

    ctx.cache.insert((offset, *var), shifted);
    shifted
}