use std::collections::HashSet;
use std::hash::Hash;
use rs2::*;
use crate::analysis::*;
use crate::lean_expr::*;

// Returns whether `to` changed.
pub fn union_sets<T: Eq + Hash + Clone>(to: &mut HashSet<T>, from: HashSet<T>) -> bool {
    let from_sub_to = from.is_subset(to);
    *to = &*to | &from;
    !from_sub_to
}

// Returns whether `to` changed.
pub fn intersect_sets<T: Eq + Hash + Clone>(to: &mut HashSet<T>, from: HashSet<T>) -> bool {
    let to_sub_from = to.is_subset(&from);
    *to = &*to & &from;
    !to_sub_from
}

// Analogous to `egg::merge_max`. Returns whether `to` changed.
pub fn merge_max<T: Ord>(to: &mut T, from: T) -> bool {
    if from > *to {
        *to = from;
        true
    } else {
        false
    }
}

// TODO: Figure out how to create the union of two hash sets properly.
pub fn union_clone<T: Eq + Hash + Copy>(fst: &HashSet<T>, snd: &HashSet<T>) -> HashSet<T> {
    let mut result = fst.clone();
    for elem in snd { result.insert(*elem); }
    return result
}

pub fn shift_down(indices: &HashSet<u64>) -> HashSet<u64> {
    let mut result = HashSet::with_capacity(indices.len());
    for &idx in indices {
        if idx == 0 {
            continue
        } else {
            result.insert(idx - 1);
        }
    }
    return result
}

// Analogous to `Pattern::vars` in egg: returns the variables of a pattern in order of appearance.
pub fn pattern_vars(pat: &LeanPattern) -> Vec<PVar> {
    let mut vars = vec![];
    collect_vars(pat, &mut vars);
    vars
}

fn collect_vars(pat: &LeanPattern, vars: &mut Vec<PVar>) {
    match pat {
        Pattern::PVar(var)     => if !vars.contains(var) { vars.push(*var) },
        Pattern::Node(_, pats) => for p in pats.iter() { collect_vars(p, vars) },
        Pattern::G(_, p)       => collect_vars(p, vars)
    }
}

// Analogous to `str.parse::<Pattern<_>>().unwrap()` in egg.
pub fn pat(str: &str) -> LeanPattern {
    parse_pattern(str).unwrap()
}

// Analogous to `str.parse::<RecExpr<_>>().unwrap()` in egg.
pub fn term(str: &str) -> LeanTerm {
    parse_term(str).unwrap()
}
