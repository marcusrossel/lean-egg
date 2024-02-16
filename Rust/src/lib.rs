use egg::*;
use core::ffi::c_char;
use core::ffi::CStr;
use std::ffi::CString;
use std::ptr::null;
use std::str::FromStr;

mod lean_expr;
use lean_expr::*;

mod nat_lit;
use nat_lit::*;

mod basic;
use basic::*;

#[repr(C)]
#[derive(PartialEq)]
pub enum RewriteDirection {
    None,
    Forward,
    Backward,
    Both
}

#[repr(C)]
pub struct CRewrite {
    name: *const c_char,
    lhs:  *const c_char,
    rhs:  *const c_char,
    dir:  RewriteDirection
}

#[repr(C)]
pub struct EggResult {
    success: bool,
    expl:    *const c_char,
}

fn rewrites_from_c(rws: &[CRewrite]) -> Vec<Rewrite<LeanExpr, NatLitAnalysis>> {
    rws.iter().fold(vec![], |mut acc, rw| {
        let name_c_str = unsafe { CStr::from_ptr(rw.name) };
        let lhs_c_str  = unsafe { CStr::from_ptr(rw.lhs) };
        let rhs_c_str  = unsafe { CStr::from_ptr(rw.rhs) };
        let name_str   = name_c_str.to_str().unwrap();
        let lhs_str    = lhs_c_str.to_str().unwrap();
        let rhs_str    = rhs_c_str.to_str().unwrap();
        let lhs        = Pattern::from_str(lhs_str).expect("Failed to parse lhs");
        let rhs        = Pattern::from_str(rhs_str).expect("Failed to parse rhs");
        if rw.dir == RewriteDirection::Forward || rw.dir == RewriteDirection::Both {
            acc.push(Rewrite::new(name_str, lhs.clone(), rhs.clone()).expect("Failed to parse rule"));
        }
        if rw.dir == RewriteDirection::Backward || rw.dir == RewriteDirection::Both {
            // It is important that we use the "-rev" suffix for reverse rules here, as this is also
            // what's used for adding the reverse rule when using egg's `rewrite!(_; _ <=> _)` macro.
            // If we choose another naming scheme, egg may complain about duplicate rules when 
            // `rw.dir == RewriteDirection::Both`. This is the case, for example, for the rewrite
            // `?a + ?b = ?b + ?a`.
            acc.push(Rewrite::new(format!("{name_str}-rev"), rhs, lhs).expect("Failed to parse rule"));
        }
        acc
    })
}

#[no_mangle]
pub extern "C" fn c_egg_explain_congr(
    init_str_ptr: *const c_char, 
    goal_str_ptr: *const c_char, 
    rws_ptr: *const CRewrite, 
    rws_count: usize,
    optimize_expl: bool,
    gen_nat_lit_rws: bool
) -> EggResult {
    // Cf. https://doc.rust-lang.org/stable/std/ffi/struct.CStr.html#examples
    let init_c_str = unsafe { CStr::from_ptr(init_str_ptr) };
    let goal_c_str = unsafe { CStr::from_ptr(goal_str_ptr) };
    let init = String::from_utf8_lossy(init_c_str.to_bytes()).to_string();
    let goal = String::from_utf8_lossy(goal_c_str.to_bytes()).to_string();
    assert!(rws_ptr != null()); 
    let c_rws = unsafe { std::slice::from_raw_parts(rws_ptr, rws_count) };
    let rws = rewrites_from_c(c_rws);
    if let Some(expl) = explain_congr(init, goal, rws, optimize_expl, gen_nat_lit_rws) {
        let expl_c_str = CString::new(expl).expect("conversion of explanation to C-string failed");
        // Note: The `into_raw` here is important, as otherwise Rust deallocates the string.
        // TODO: I think this is a memory leak right now.
        EggResult { success: true,  expl: expl_c_str.into_raw() }
    } else {
        EggResult { success: false, expl: null() }
    }
}