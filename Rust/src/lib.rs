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

#[repr(C)]
pub struct CStringArray {
    ptr: *const *const c_char,
    len: usize, 
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

fn rw_templates_from_c(rws: &[CRewrite]) -> Res<Vec<RewriteTemplate>> {
    let mut res: Vec<RewriteTemplate> = vec![];
    for rw in rws {
        let name_c_str = unsafe { CStr::from_ptr(rw.name) };
        let lhs_c_str  = unsafe { CStr::from_ptr(rw.lhs) };
        let rhs_c_str  = unsafe { CStr::from_ptr(rw.rhs) };
        let name_str   = name_c_str.to_str().unwrap();
        let lhs_str    = lhs_c_str.to_str().unwrap();
        let rhs_str    = rhs_c_str.to_str().unwrap();
        let lhs        = Pattern::from_str(lhs_str).expect("Failed to parse lhs");
        let rhs        = Pattern::from_str(rhs_str).expect("Failed to parse rhs");
        if rw.dirs == RewriteDirections::Forward || rw.dirs == RewriteDirections::Both {
            res.push(RewriteTemplate { name: name_str.to_string(), lhs: lhs.clone(), rhs: rhs.clone() })
        }
        if rw.dirs == RewriteDirections::Backward || rw.dirs == RewriteDirections::Both {
            // It is important that we use the "-rev" suffix for reverse rules here, as this is also
            // what's used for adding the reverse rule when using egg's `rewrite!(_; _ <=> _)` macro.
            // If we choose another naming scheme, egg may complain about duplicate rules when 
            // `rw.dir == RewriteDirection::Both`. This is the case, for example, for the rewrite
            // `?a + ?b = ?b + ?a`.
            res.push(RewriteTemplate { name: format!("{name_str}-rev"), lhs: rhs, rhs: lhs })
        }
    }
    Ok(res)
}

#[no_mangle]
pub extern "C" fn egg_explain_congr(
    init_str_ptr: *const c_char, 
    goal_str_ptr: *const c_char, 
    rws: CRewritesArray, 
    facts: CStringArray, 
    guides: CStringArray, 
    cfg: Config,
    viz_path_ptr: *const c_char
) -> *const c_char {
    // Cf. https://doc.rust-lang.org/stable/std/ffi/struct.CStr.html#examples
    let init_c_str = unsafe { CStr::from_ptr(init_str_ptr) };
    let goal_c_str = unsafe { CStr::from_ptr(goal_str_ptr) };
    let init = String::from_utf8_lossy(init_c_str.to_bytes()).to_string();
    let goal = String::from_utf8_lossy(goal_c_str.to_bytes()).to_string();
    let c_rws = unsafe { std::slice::from_raw_parts(rws.ptr, rws.len) };
    let c_facts = unsafe { std::slice::from_raw_parts(facts.ptr, facts.len) };
    let c_guides = unsafe { std::slice::from_raw_parts(guides.ptr, guides.len) };

    // Note: The `into_raw`s below are important, as otherwise Rust deallocates the string.
    // TODO: I think this is a memory leak right now.

    let rw_templates = rw_templates_from_c(c_rws);
    if let Err(rws_err) = rw_templates { 
        let rws_err_c_str = CString::new(rws_err.to_string()).expect("conversion of error message to C-string failed");
        return rws_err_c_str.into_raw()
    }
    let rw_templates = rw_templates.unwrap();

    let guides = c_guides.iter().map(|&guide_c_str| {
        let c_str = unsafe { CStr::from_ptr(guide_c_str) };
        String::from_utf8_lossy(c_str.to_bytes()).to_string()
    }).collect();    

    let viz_path_c_str = unsafe { CStr::from_ptr(viz_path_ptr) };
    let raw_viz_path = String::from_utf8_lossy(viz_path_c_str.to_bytes()).to_string();
    let viz_path = if raw_viz_path.is_empty() { None } else { Some(raw_viz_path) };

    let expl = explain_congr(init, goal, rw_templates, guides, cfg, viz_path);
    if let Err(expl_err) = expl {
        let rws_err_c_str = CString::new(expl_err.to_string()).expect("conversion of error message to C-string failed");
        return rws_err_c_str.into_raw()
    }
    let expl = expl.unwrap();

    let expl_c_str = CString::new(expl).expect("conversion of explanation to C-string failed");
    expl_c_str.into_raw()
}