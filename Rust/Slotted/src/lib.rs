use slotted_egraphs::*;
use core::ffi::c_char;
use core::ffi::CStr;
use std::ffi::CString;
use std::ptr::null;
use libc::c_double;
use basic::*;
use analysis::*;
use result::*;
use rewrite::*;

mod analysis;
mod basic;
mod beta;
mod eta;
mod lean_expr;
mod levels;
mod nat_lit;
mod result;
mod rewrite;

// Cf. https://doc.rust-lang.org/stable/std/ffi/struct.CStr.html#examples
fn c_str_to_string(c_str: *const c_char) -> String {
    let str = unsafe { CStr::from_ptr(c_str) };
    String::from_utf8_lossy(str.to_bytes()).to_string()
}

// TODO: I think this is a memory leak right now.
fn string_to_c_str(str: String) -> *const c_char {
    let expl_c_str = CString::new(str).expect("conversion of Rust-string to C-string failed");
    expl_c_str.into_raw()
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
            let lhs           = Pattern::parse(lhs_str).expect("Failed to parse lhs");
            let rhs           = Pattern::parse(rhs_str).expect("Failed to parse rhs");
            let conds: Vec<_> = conds_strs.iter().map(|cond| Pattern::parse(cond).expect("Failed to parse condition")).collect();

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
pub enum CStopReason {
    Saturated,
    TimeLimit,
    IterationLimit,
    NodeLimit,
    Other,
}

impl CStopReason {

    fn from_stop_reason(r: StopReason) -> CStopReason {
        match r {
            StopReason::Saturated      => CStopReason::Saturated,
            StopReason::IterationLimit => CStopReason::IterationLimit,
            StopReason::TimeLimit      => CStopReason::TimeLimit,
            StopReason::Other(_)       => CStopReason::Other,
        }
    }
}

#[repr(C)]
pub struct CReport {
    iterations:     usize,
    stop_reason:    CStopReason,
    egraph_nodes:   usize,
    egraph_classes: usize,
    total_time:     c_double,
    rw_stats:       *const c_char,
}

impl CReport {

    fn from_report(r: Report) -> CReport {
        CReport {
            iterations:     r.iterations,
            stop_reason:    CStopReason::from_stop_reason(r.stop_reason),
            egraph_nodes:   r.egraph_nodes,
            egraph_classes: r.egraph_classes,
            total_time:     r.total_time,
            rw_stats:       string_to_c_str("".to_string()),
        }
    }

    fn none() -> CReport {
        CReport {
            iterations:     0,
            stop_reason:    CStopReason::Other,
            egraph_nodes:   0,
            egraph_classes: 0,
            total_time:     0.0,
            rw_stats:       null(),
        }
    }
}

#[repr(C)]
pub struct EqsatResult {
    expl: *const c_char,
    graph: Option<Box<LeanEGraph>>,
    report: CReport
}

#[no_mangle]
pub extern "C" fn slotted_explain_congr(
    init_str_ptr: *const c_char, 
    goal_str_ptr: *const c_char, 
    rws: CRewritesArray, 
    guides: CStringArray, 
    cfg: Config,
    viz_path_ptr: *const c_char
) -> EqsatResult {
    let init   = c_str_to_string(init_str_ptr);
    let goal   = c_str_to_string(goal_str_ptr);
    let guides = guides.to_vec();

    // Note: The `into_raw`s below are important, as otherwise Rust deallocates the string.
    // TODO: I think this is a memory leak right now.

    let rw_templates = rws.to_templates();
    if let Err(rws_err) = rw_templates { 
        return EqsatResult { expl: string_to_c_str(rws_err.to_string()), graph: None, report: CReport::none() }
    }
    let rw_templates = rw_templates.unwrap();

    let viz_path_c_str = unsafe { CStr::from_ptr(viz_path_ptr) };
    let raw_viz_path = String::from_utf8_lossy(viz_path_c_str.to_bytes()).to_string();
    let viz_path = if raw_viz_path.is_empty() { None } else { Some(raw_viz_path) };

    let res = explain_congr(init, goal, rw_templates, guides, cfg, viz_path);
    if let Err(res_err) = res {
        return EqsatResult { expl: string_to_c_str(res_err.to_string()), graph: None, report: CReport::none() }
    }
    let (expl, egraph, report) = res.unwrap();

    return EqsatResult {
        expl: string_to_c_str(expl),
        graph: Some(Box::new(egraph)),
        report: CReport::from_report(report) 
    }
}

#[no_mangle]
pub unsafe extern "C" fn slotted_query_equiv(
    egraph: *mut LeanEGraph,
    init_str_ptr: *const c_char, 
    goal_str_ptr: *const c_char
) -> *const c_char {
    let egraph = egraph.as_mut().unwrap();
    let init = RecExpr::parse(&c_str_to_string(init_str_ptr)).unwrap();
    let goal = RecExpr::parse(&c_str_to_string(goal_str_ptr)).unwrap();
    let init_id = egraph.add_expr(init.clone());
    let goal_id = egraph.add_expr(goal.clone());

    if egraph.eq(&init_id, &goal_id) {
        let expl = egraph.explain_equivalence(init, goal).to_flat_string(&egraph);
        string_to_c_str(expl)
    } else {
        string_to_c_str("".to_string())
    }
}

#[no_mangle]
pub unsafe extern "C" fn slotted_free_egraph(egraph: *mut LeanEGraph) {
    if !egraph.is_null() { drop(Box::from_raw(egraph)); }
}