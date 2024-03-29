use std::collections::HashSet;
use std::hash::Hash;
//use std::ffi::c_char;
//use std::ffi::CString;
use egg::*;

// TODO: Remove this when eta-reduction seems stable.
//
// extern "C" {
//     fn c_dbg_trace(str: *const c_char);
// }

pub fn dbg_trace<T: ToString>(_obj: T) {
    // let str = obj.to_string();
    // let c_str = CString::new(str).expect("conversion of explanation to C-string failed");
    // unsafe { c_dbg_trace(c_str.into_raw()) }
}

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