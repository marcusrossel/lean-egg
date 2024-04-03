use std::collections::HashSet;
use std::hash::Hash;
use egg::*;

pub fn union_sets<T: Eq + Hash + Clone>(to: &mut HashSet<T>, from: HashSet<T>) -> DidMerge {
    let to_sub_from = to.is_subset(&from);
    let from_sub_to = from.is_subset(to);
    *to = &*to | &from;
    match (to_sub_from, from_sub_to) {
        (false, false) => DidMerge(true,  true),
        (false, true)  => DidMerge(false, true),
        (true,  false) => DidMerge(true,  false),
        (true,  true)  => DidMerge(false, false)
    }
}

// TODO: Figure out how to create the union of two hash sets properly.
pub fn union_clone<T: Eq + Hash + Copy>(fst: &HashSet<T>, snd: &HashSet<T>) -> HashSet<T> {
    let mut result = fst.clone();
    for elem in snd { result.insert(*elem); }
    return result
}

// TODO: Figure out how to fold over a hashset.
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