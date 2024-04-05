
use std::collections::HashMap;
use egg::*;
use crate::lean_expr::*;
use crate::analysis::*;

// An expression position is a sequence of coordinates which describe how to traverse nodes
// starting at a given root node. Each coordinate dictates which child of a node to visit. 
// In an expression tree, each node has a unique position.
type ExprPos = Vec<usize>; 
// A binder position of `None` indicates that the associated value does not appear under a binder.
type BinderPos = Option<ExprPos>;

// The given values are always used together in `match_is_valid_core`, so we given them a type.
struct Location {
    pos:           ExprPos,
    parent_binder: BinderPos, 
    binder_depth:  u64
}

// Various data required for checking match validity.
struct Context<'a> {
    pat:            &'a PatternAst<LeanExpr>,
    subst:          &'a Subst,
    graph:          &'a LeanEGraph,
    parent_binders: HashMap<Var, BinderPos>
}

// A match (a substitution and pattern) is valid if both:
// (1) No (non-loose) bound variables are matched.
// (2) For each variable v in the substitution which maps to an e-class with loose bvars, 
//     v only appears under the same binder.
//
// Example of invalid matches: 
// (1) Pattern term `(lam _, ?x)` matching against `(lam _, (bvar 0))`.
// (2) Pattern term `(lam _ (lam _, ?x) ?x)` matching against `(lam _ (lam _, (bvar 2)) (bvar 2))`.
//
// The need for Condition (2) should be obvious. Condition (1) on the other hand only follows from
// the fact that our rewrites come from theorems of the form `forall x, y = z`. Thus, if a pattern
// variable appears, it can never refer to a (non-loose) bound variable, as `x` cannot refer to any
// bound variables in `y` or `z`.
pub fn match_is_valid(subst: &Subst, pat: &PatternAst<LeanExpr>, graph: &LeanEGraph) -> bool {
    let mut ctx = Context { pat, subst, graph, parent_binders: HashMap::new() };
    let root_idx = pat.as_ref().len() - 1;
    let loc = Location { pos: vec![], parent_binder: None, binder_depth: 0 };
    match_is_valid_core(root_idx, loc, &mut ctx)
}

fn match_is_valid_core(idx: usize, loc: Location, ctx: &mut Context) -> bool {
    match &ctx.pat.as_ref()[idx] {
        ENodeOrVar::Var(var) => {
            let loose_bvars = &ctx.graph[ctx.subst[*var]].data.loose_bvars;
            if loose_bvars.is_empty() { 
                // If the given variable does not map to an e-class containing loose bvars, if cannot cause any problems.
                return true 
            } else {
                // If the given variable maps to an e-class containing loose bvars, we need to check Conditions (1) and (2).

                // For Condition (1): If the variable maps to an e-class containing bound variables whose indices are 
                // exceeded by the current binder depth, then those bound variables must be non-loose in the context
                // of `ctx.pat`, and are not allowed to be matched.
                if loose_bvars.iter().any(|b| *b < loc.binder_depth) { return false }

                if let Some(required_parent) = ctx.parent_binders.get(var) {
                    // For Condition (2): If the variable has already occured elsewhere in the pattern, 
                    // then the parent binder of that occurrence must be the same as the current parent binder.
                    return loc.parent_binder == *required_parent
                } else {
                    // If the given variable has not been visited yet, record its parent binder.
                    ctx.parent_binders.insert(*var, loc.parent_binder);
                    return true
                }
            }
        },
        ENodeOrVar::ENode(e) => {
            for (i, child) in e.children().iter().enumerate() {
                // If `e` is a binder, set the parent binder and increase the binder depth for its body.
                let (parent_binder, binder_depth) = 
                    if e.is_binder() && i == 1 { 
                        (Some(loc.pos.clone()), loc.binder_depth + 1) 
                    } else { 
                        (loc.parent_binder.clone(), loc.binder_depth) 
                    };
                let mut pos = loc.pos.clone(); pos.push(i);
                let child_loc = Location { pos, parent_binder, binder_depth };

                let child_idx = usize::from(*child);
                if !match_is_valid_core(child_idx, child_loc, ctx) { return false }
            }
            true
        }
    }
}
