use std::ffi::c_char;
use std::ffi::CString;
use std::collections::HashSet;
use std::hash::Hash;

extern "C" {
    fn c_dbg_trace(str: *const c_char);
}

static mut ENABLED_TRACE_GROUPS: Option<HashSet<TraceGroup>> = None;

#[derive(PartialEq, Eq, Hash)]
pub enum TraceGroup {
    Subst,
    BVarCorrection
}

pub fn init_enabled_trace_groups(trace_substitutions: bool, trace_bvar_correction: bool) {
    let mut enabled: HashSet<TraceGroup> = HashSet::new();
    if trace_substitutions { enabled.insert(TraceGroup::Subst); }
    if trace_bvar_correction { enabled.insert(TraceGroup::BVarCorrection); }
    unsafe { ENABLED_TRACE_GROUPS = Some(enabled) }
}

pub fn dbg_trace<T: ToString>(obj: T, group: TraceGroup) {
    unsafe { 
        if let Some(enabled) = &ENABLED_TRACE_GROUPS { 
            if !enabled.contains(&group) { return } 
        } 
    }

    let str = obj.to_string();
    let c_str = CString::new(str).expect("conversion of explanation to C-string failed");
    unsafe { c_dbg_trace(c_str.into_raw()) }
}