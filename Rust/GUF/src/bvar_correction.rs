use std::collections::HashMap;
use rs2::*;
use crate::lean_expr::*;
use crate::analysis::*;
use crate::proof::*;

// Given a pattern and a substitution, returns an adjusted pattern, such that applying the substitution
// to the pattern yields the same result except that loose bound variable indices are shifted such that
// they keep referring to the same loose bound variables. This procedure requires a map of the binder
// depths for each variable (which maps to loose bound variables) in the LHS of a given rewrite. This is
// necessary to correctly interpret the meaning of bound variables in the given `subst`.
//
// This, for example, solves invalid capture of bound variables. But it is also necessary to correctly
// perform the following rewrite:
//
// (lam _ (lam _ ?x) 0) 0 => (lam _ ?x) 0
// matched against
// (lam _ (lam _ (bvar 5)) 0) 0
// needs to become
// (lam _ (bvar 4)) 0
pub fn correct_bvar_indices(pat: &LeanPattern, var_depths: HashMap<PVar, u64>) -> LeanPattern {
    correct_bvar_indices_core(pat, 0, &var_depths)
}

// Traverses the given pattern while constructing an analogous one which adds shifting for all variables
// which would otherwise result in invalid bound variable capture of invalid loose bound variable creation.
fn correct_bvar_indices_core(pat: &LeanPattern, binder_depth: u64, var_depths: &HashMap<PVar, u64>) -> LeanPattern {
    match pat {
        Pattern::PVar(var) => {
            let offset = if let Some(var_depth) = var_depths.get(var) {
                (binder_depth as i64) - (*var_depth as i64)
            } else {
                0
            };

            // Note that a value of `0` indicates either an absence of loose bvars in the class of `var`,
            // or an actual offset of `0`.
            if offset == 0 {
                // If the given variable maps to an expression that does not contain loose bvars,
                // or if the binder depth of that variable has not changed, then we can keep it as is.
                pat.clone()
            } else {
                // Otherwise, shift the variable by the required offset.
                let dir = if offset >= 0 { "+" } else { "-" };
                Pattern::Node(LeanExpr::Shift(std::array::from_fn(|_| nil())), Box::new([
                    leaf(LeanExpr::Str(dir.to_string())),
                    leaf(LeanExpr::Nat(offset.unsigned_abs())),
                    leaf(LeanExpr::Nat(0)),
                    pat.clone()
                ]))
            }
        },
        Pattern::Node(e, children) => {
            let children = children.iter().enumerate().map(|(i, child)| {
                // If `e` is a binder, increase the binder depth for its body.
                let child_binder_depth = if e.is_binder() && i == 1 { binder_depth + 1 } else { binder_depth };
                correct_bvar_indices_core(child, child_binder_depth, var_depths)
            }).collect();
            Pattern::Node(e.clone(), children)
        },
        Pattern::G(..) => unreachable!("patterns are not proof-annotated")
    }
}

fn leaf(node: LeanExpr) -> LeanPattern {
    Pattern::Node(node, Box::new([]))
}
