use std::collections::HashSet;
use std::hash::Hash;
use egg::*;

pub fn merge_sets<T: Eq + Hash>(to: &mut HashSet<T>, from: HashSet<T>) -> DidMerge {
    let to_sub_from = to.is_subset(&from);
    let from_sub_to = from.is_subset(to);
    to.extend(from);
    match (to_sub_from, from_sub_to) {
        (false, false) => DidMerge(true,  true),
        (false, true)  => DidMerge(false, true),
        (true,  false) => DidMerge(true,  false),
        (true,  true)  => DidMerge(false, false)
    }
}
