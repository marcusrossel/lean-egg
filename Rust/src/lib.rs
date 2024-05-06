use analysis::LeanEGraph;
use egg::*;
use core::ffi::c_char;
use core::ffi::CStr;
use std::ffi::CString;
use std::str::FromStr;
use basic::*;
use result::*;
use rewrite::*;

mod analysis;
mod basic;
mod beta;
mod bvar_correction;
mod eta;
mod lean_expr;
mod nat_lit;
mod result;
mod rewrite;
mod shift_loose;
mod subst;
mod trace;
mod util;
mod valid_match;

// Cf. https://doc.rust-lang.org/stable/std/ffi/struct.CStr.html#examples
fn c_str_to_string(c_str: *const c_char) -> String {
    let str = unsafe { CStr::from_ptr(c_str) };
    String::from_utf8_lossy(str.to_bytes()).to_string()
}

#[repr(C)]
pub struct CStringArray {
    ptr: *const *const c_char,
    len: usize, 
}

impl CStringArray {

    fn to_vec(&self) -> Vec<String> {
        let slice = unsafe { std::slice::from_raw_parts(self.ptr, self.len) };
        slice.iter().map(|&str_ptr| c_str_to_string(str_ptr)).collect()
    }
}

#[repr(C)]
#[derive(PartialEq)]
pub enum RewriteDirections {
    None,
    Forward,
    Backward,
    Both
}

#[repr(C)]
pub struct CRewrite {
    name:  *const c_char,
    lhs:   *const c_char,
    rhs:   *const c_char,
    dirs:  RewriteDirections,
    conds: CStringArray
}

#[repr(C)]
pub struct CRewritesArray {
    ptr: *const CRewrite,
    len: usize, 
}

impl CRewritesArray {

    fn to_templates(&self) -> Res<Vec<RewriteTemplate>> {
        let rws = unsafe { std::slice::from_raw_parts(self.ptr, self.len) };
        let mut res: Vec<RewriteTemplate> = vec![];
        
        for rw in rws {
            let name_c_str    = unsafe { CStr::from_ptr(rw.name) };
            let lhs_c_str     = unsafe { CStr::from_ptr(rw.lhs) };
            let rhs_c_str     = unsafe { CStr::from_ptr(rw.rhs) };
            let name_str      = name_c_str.to_str().unwrap();
            let lhs_str       = lhs_c_str.to_str().unwrap();
            let rhs_str       = rhs_c_str.to_str().unwrap();
            let conds_strs    = rw.conds.to_vec();
            let lhs           = Pattern::from_str(lhs_str).expect("Failed to parse lhs");
            let rhs           = Pattern::from_str(rhs_str).expect("Failed to parse rhs");
            let conds: Vec<_> = conds_strs.iter().map(|cond| Pattern::from_str(cond).expect("Failed to parse condition")).collect();

            if rw.dirs == RewriteDirections::Forward || rw.dirs == RewriteDirections::Both {
                res.push(RewriteTemplate { name: name_str.to_string(), lhs: lhs.clone(), rhs: rhs.clone(), conds: conds.clone() })
            }
            if rw.dirs == RewriteDirections::Backward || rw.dirs == RewriteDirections::Both {
                // It is important that we use the "-rev" suffix for reverse rules here, as this is also
                // what's used for adding the reverse rule when using egg's `rewrite!(_; _ <=> _)` macro.
                // If we choose another naming scheme, egg may complain about duplicate rules when 
                // `rw.dir == RewriteDirection::Both`. This is the case, for example, for the rewrite
                // `?a + ?b = ?b + ?a`.
                res.push(RewriteTemplate { name: format!("{name_str}-rev"), lhs: rhs, rhs: lhs, conds })
            }
        }
        Ok(res)
    }
}

#[repr(C)]
pub struct CFact {
    name: *const c_char,
    expr: *const c_char
}

#[repr(C)]
pub struct CFactsArray {
    ptr: *const CFact,
    len: usize, 
}

impl CFactsArray {

    fn to_vec(&self) -> Vec<(String, String)> {
        let slice = unsafe { std::slice::from_raw_parts(self.ptr, self.len) };
        slice.iter().map(|fact| {
            let name = c_str_to_string(fact.name);
            let expr = c_str_to_string(fact.expr);
            (name, expr)
        }).collect()
    }
}

#[repr(C)]
pub struct EggResult {
    expl: *const c_char,
    graph: Option<Box<LeanEGraph>>,
}

#[no_mangle]
pub extern "C" fn egg_explain_congr(
    init_str_ptr: *const c_char, 
    goal_str_ptr: *const c_char, 
    rws: CRewritesArray, 
    facts: CFactsArray, 
    guides: CStringArray, 
    cfg: Config,
    viz_path_ptr: *const c_char
) -> EggResult {
    let init   = c_str_to_string(init_str_ptr);
    let goal   = c_str_to_string(goal_str_ptr);
    let guides = guides.to_vec();
    let facts  = facts.to_vec();

    // Note: The `into_raw`s below are important, as otherwise Rust deallocates the string.
    // TODO: I think this is a memory leak right now.

    let rw_templates = rws.to_templates();
    if let Err(rws_err) = rw_templates { 
        let rws_err_c_str = CString::new(rws_err.to_string()).expect("conversion of error message to C-string failed");
        return EggResult { expl: rws_err_c_str.into_raw(), graph: None }
    }
    let rw_templates = rw_templates.unwrap();

    let viz_path_c_str = unsafe { CStr::from_ptr(viz_path_ptr) };
    let raw_viz_path = String::from_utf8_lossy(viz_path_c_str.to_bytes()).to_string();
    let viz_path = if raw_viz_path.is_empty() { None } else { Some(raw_viz_path) };

    let res = explain_congr(init, goal, rw_templates, facts, guides, cfg, viz_path);
    if let Err(res_err) = res {
        let res_err_c_str = CString::new(res_err.to_string()).expect("conversion of error message to C-string failed");
        return EggResult { expl: res_err_c_str.into_raw(), graph: None }
    }
    let (expl, egraph) = res.unwrap();
    
    let expl_c_str = CString::new(expl).expect("conversion of explanation to C-string failed");

    return EggResult {
        expl: expl_c_str.into_raw(),
        graph: Some(Box::new(egraph))
    }
}

#[no_mangle]
pub unsafe extern "C" fn egg_query_equiv(
    egraph: *mut LeanEGraph,
    init_str_ptr: *const c_char, 
    goal_str_ptr: *const c_char
) -> *const c_char {
    let egraph = egraph.as_mut().unwrap();
    let init = c_str_to_string(init_str_ptr).parse().unwrap();
    let goal = c_str_to_string(goal_str_ptr).parse().unwrap();
    let init_id = egraph.add_expr(&init);
    let goal_id = egraph.add_expr(&goal);

    if egraph.find(init_id) == egraph.find(goal_id) {
        let mut expl = egraph.explain_equivalence(&init, &goal);
        let expl_str = expl.get_flat_string();
        let expl_c_str = CString::new(expl_str.to_string()).expect("conversion of explanation to C-string failed");
        expl_c_str.into_raw()
    } else {
        CString::new("").unwrap().into_raw()
    }
}

#[no_mangle]
pub unsafe extern "C" fn free_egraph(egraph: *mut LeanEGraph) {
    if !egraph.is_null() { drop(Box::from_raw(egraph)); }
}