use analysis::LeanEGraph;
use egg::*;
use expl::{mk_explanation, ExplanationKind};
use lean_expr::LeanExpr;
use util::sub_expr;
use std::{collections::HashSet, ffi::{c_char, c_void, CStr, CString}};
use libc::c_double;
use std::str::FromStr;
use activation::*;
use basic::*;
use result::*;
use rewrite::*;

mod activation;
mod analysis;
mod basic;
mod beta;
mod bvar_correction;
mod eta;
mod lean_expr;
mod levels;
mod expl;
mod nat_lit;
mod result;
mod rewrite;
mod shift;
mod subst;
mod util;
mod valid_match;

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
pub struct CRewrite {
    name:  *const c_char,
    lhs:   *const c_char,
    rhs:   *const c_char,
    conds: CStringArray
}

#[repr(C)]
pub struct CRewritesArray {
    ptr: *const CRewrite,
    len: usize, 
}

impl CRewritesArray {

    fn to_templates(&self, blocks: Vec<RecExpr<LeanExpr>>) -> Res<Vec<RewriteTemplate>> {
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
            
            let mut prop_conds: Vec<Pattern<LeanExpr>> = vec![];
            let mut tc_conds = vec![];
            for str in conds_strs {
                let pat: Pattern<_> = str.parse().map_err(|e : RecExprParseError<_>| Error::Condition(e.to_string()))?;
                let head = Id::from(pat.ast.as_ref().len() - 1);
                match &pat.ast[head] {
                    ENodeOrVar::ENode(LeanExpr::Proof(prop)) => prop_conds.push(sub_expr(&pat.ast, *prop).into()),
                    ENodeOrVar::ENode(LeanExpr::Inst(class)) => tc_conds.push(sub_expr(&pat.ast, *class).into()),
                    _ => return Err(Error::Condition("Received condition without 'proof' or 'inst' prefix.".to_string()))
                }
            }

            // Computes the set of "weak" vars, which appear in a prop condition, but not the lhs.
            let mut prop_vars: HashSet<Var> = Default::default();
            for prop_cond in &prop_conds {
                for var in prop_cond.vars() {
                    prop_vars.insert(var);
                }
            }
            prop_vars.retain(|var| !lhs.vars().contains(var));
            let mut weak_vars: Vec<Var> = prop_vars.into_iter().collect();
            weak_vars.sort();

            res.push(RewriteTemplate { 
                name:       name_str.to_string(), 
                lhs:        lhs.clone(), 
                rhs:        rhs.clone(), 
                prop_conds: prop_conds.clone(),
                tc_conds:   tc_conds.clone(),
                weak_vars:  weak_vars.clone(),
                blocks:     blocks.clone()
            });
        }
        Ok(res)
    }
}


pub fn u8_from_stop_reason(r: StopReason) -> (u8, String) {
    match r {
        StopReason::Saturated         => (0, "".to_string()),
        StopReason::TimeLimit(_)      => (1, "".to_string()),
        StopReason::IterationLimit(_) => (2, "".to_string()),
        StopReason::NodeLimit(_)      => (3, "".to_string()),
        StopReason::Other(msg)        => (4, msg),
    }
}

#[repr(C)]
pub struct CReport {
    iterations:      usize,
    stop_reason:     u8,
    stop_reason_msg: *const c_char,
    egraph_nodes:    usize,
    egraph_classes:  usize,
    total_time:      c_double,
    rw_stats:        *const c_char,
    activations:     *const c_char
}

impl CReport {

    fn from_report(r: Report, rw_stats: String, activations: Activations) -> CReport {
        let (stop_reason, msg) = u8_from_stop_reason(r.stop_reason);
        CReport {
            iterations:      r.iterations,
            stop_reason:     stop_reason,
            stop_reason_msg: string_to_c_str(msg),
            egraph_nodes:    r.egraph_nodes,
            egraph_classes:  r.egraph_classes,
            total_time:      r.total_time,
            rw_stats:        string_to_c_str(rw_stats),
            activations:     string_to_c_str(activations.report())
        }
    }

    fn from_other_stop_reason(msg: String) -> CReport {
        CReport {
            iterations:      0,
            stop_reason:     u8_from_stop_reason(StopReason::Other(String::new())).0,
            stop_reason_msg: string_to_c_str(msg),
            egraph_nodes:    0,
            egraph_classes:  0,
            total_time:      0.0,
            rw_stats:        string_to_c_str("".to_string()),
            activations:     string_to_c_str("".to_string())
        }
    }
}

#[repr(C)]
pub struct EqsatResult {
    kind: u8,
    expl: *const c_char,
    graph: Option<Box<LeanEGraph>>,
    report: CReport
}

#[no_mangle]
pub extern "C" fn egg_explain_congr(
    init_str_ptr: *const c_char, 
    goal_str_ptr: *const c_char, 
    rws: CRewritesArray, 
    guides: CStringArray, 
    blocks: CStringArray, 
    cfg: Config,
    viz_path_ptr: *const c_char,
    env: *const c_void,
) -> EqsatResult {
    let init   = c_str_to_string(init_str_ptr);
    let goal   = c_str_to_string(goal_str_ptr);
    let guides = guides.to_vec();
    let blocks = blocks.to_vec().iter().map(|block| block.parse().unwrap()).collect();

    let rw_templates = rws.to_templates(blocks);
    if let Err(rws_err) = rw_templates { 
        return EqsatResult { 
            kind: ExplanationKind::None.to_c(), 
            expl: string_to_c_str(rws_err.to_string()), 
            graph: None, 
            report: CReport::from_other_stop_reason(rws_err.to_string()) 
        }
    }
    let rw_templates = rw_templates.unwrap();

    let raw_viz_path = c_str_to_string(viz_path_ptr);
    let viz_path = if raw_viz_path.is_empty() { None } else { Some(raw_viz_path) };

    let res = explain_congr(init, goal, rw_templates, guides, cfg, viz_path, env);
    if let Err(res_err) = res {
        return EqsatResult { 
            kind: ExplanationKind::None.to_c(),
            expl: string_to_c_str(res_err.to_string()), 
            graph: None, 
            report: CReport::from_other_stop_reason(res_err.to_string()) 
        }
    }
    let ExplainedCongr { kind, expl, egraph, report, rw_stats, activations } = res.unwrap();

    EqsatResult {
        kind: kind.to_c(),
        expl: string_to_c_str(expl),
        graph: Some(Box::new(egraph)),
        report: CReport::from_report(report, rw_stats, activations) 
    }
}

#[no_mangle]
pub unsafe extern "C" fn egg_query_equiv(
    egraph: *mut LeanEGraph,
    init_str_ptr: *const c_char, 
    goal_str_ptr: *const c_char
) -> EqsatResult {
    let egraph    = egraph.as_mut().unwrap();
    let init_expr = c_str_to_string(init_str_ptr).parse().unwrap();
    let goal_expr = c_str_to_string(goal_str_ptr).parse().unwrap();
    let kind: ExplanationKind;
    let expl: String;

    if let (Some(init_id), Some(goal_id)) = (egraph.lookup_expr(&init_expr), egraph.lookup_expr(&goal_expr)) {
        (kind, expl) = mk_explanation(egraph, init_expr, goal_expr, init_id, goal_id);
    } else {
        (kind, expl) = (ExplanationKind::None, "".to_string());
    }

    EqsatResult {
        kind: kind.to_c(),
        expl: string_to_c_str(expl),
        graph: None,
        report: CReport::from_other_stop_reason("".to_string())
    }
}

#[no_mangle]
pub unsafe extern "C" fn egg_get_term(egraph: *mut LeanEGraph, enode: usize) -> *const c_char {
    string_to_c_str(egraph.as_mut().unwrap().id_to_expr(Id::from(enode)).to_string())
}

#[no_mangle]
pub unsafe extern "C" fn egg_free_egraph(egraph: *mut LeanEGraph) {
    if !egraph.is_null() { drop(Box::from_raw(egraph)); }
}

extern "C" {
    fn is_synthable(env: *const c_void, tc_type_str: *const c_char) -> bool;
}
