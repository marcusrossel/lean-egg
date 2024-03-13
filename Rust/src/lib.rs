use lean_sys::*;
use egg::*;
use std::str::FromStr;
use std::ffi::CString;
use analysis::*;
use basic::*;
use result::*;

mod analysis;
mod basic;
mod beta;
mod eta;
mod lean_expr;
mod nat_lit;
mod result;
mod replace_bvars;
mod util;

#[derive(PartialEq)]
pub enum RewriteDirection {
    None,
    Forward,
    Backward,
    Both
}

impl TryFrom<usize> for RewriteDirection {
    type Error = ();

    fn try_from(i: usize) -> Result<Self, Self::Error> {
        match i {
            x if x == RewriteDirection::None     as usize => Ok(RewriteDirection::None),
            x if x == RewriteDirection::Forward  as usize => Ok(RewriteDirection::Forward),
            x if x == RewriteDirection::Backward as usize => Ok(RewriteDirection::Backward),
            x if x == RewriteDirection::Both     as usize => Ok(RewriteDirection::Both),
            _ => Err(()),
        }
    }
}

fn rewrites_from(name: String, lhs: String, rhs: String, dir: RewriteDirection) -> Res<Vec<LeanRewrite>> {
    let mut res: Vec<LeanRewrite> = vec![];
    let lhs = Pattern::from_str(&lhs).expect("Failed to parse lhs");
    let rhs = Pattern::from_str(&rhs).expect("Failed to parse rhs");
    if dir == RewriteDirection::Forward || dir == RewriteDirection::Both {
        match Rewrite::new(&name, lhs.clone(), rhs.clone()) {
            Ok(r) => res.push(r),
            Err(err) => return Err(Error::Rewrite(err.to_string()))
        }
    }
    if dir == RewriteDirection::Backward || dir == RewriteDirection::Both {
        // It is important that we use the "-rev" suffix for reverse rules here, as this is also
        // what's used for adding the reverse rule when using egg's `rewrite!(_; _ <=> _)` macro.
        // If we choose another naming scheme, egg may complain about duplicate rules when 
        // `rw.dir == RewriteDirection::Both`. This is the case, for example, for the rewrite
        // `?a + ?b = ?b + ?a`.
        match Rewrite::new(format!("{}-rev", &name), rhs, lhs) {
            Ok(r) => res.push(r),
            Err(err) => return Err(Error::Rewrite(err.to_string()))
        }
    }
    Ok(res)
}

unsafe fn lean_string_to_rust(lean_str: lean_obj_arg) -> String {
    let str_ptr = lean_string_cstr(lean_str);
    let str_len = lean_string_len(lean_str);
    let chars   = std::slice::from_raw_parts(str_ptr, str_len);
    String::from_utf8_lossy(chars).to_string()
}

unsafe fn rust_string_to_lean(rust_str: String) -> lean_obj_res {
    let c_str = CString::new(rust_str).expect("conversion of explanation to C-string failed");
    let bytes = c_str.as_bytes_with_nul();
    lean_mk_string(bytes.as_ptr())
}


// `init`: string
// `goal`: string
// `rw_names`: array of strings containing the names of rewrites
// `rw_lhss`: array of strings containing the left-hands sides of rewrites
// `rw_rhss`: array of strings containing the right-hands sides of rewrites
// `rw_dirs`: array of uint8_t containing the directions (cf. `rw_dir`) of rewrites
// `optimize_expl`: boolean indicating whether egg should try to shorten its explanations
// `gen_nat_lit_rws`: boolean indicating whether egg should use additional rewrites to convert between nat-lits and `Nat.zero`/`Nat.succ`
// `gen_eta_rw`: boolean indicating whether egg should use an additional rewrite to perform eta-reduction
// `gen_beta_rw`: boolean indicating whether egg should use an additional rewrite to perform beta-reduction
// `viz_path`: string
// return value: string explaining the rewrite sequence
#[no_mangle]
pub unsafe extern "C" fn egg_explain_congr(
    init: lean_obj_arg, 
    goal: lean_obj_arg, 
    rw_names: lean_obj_arg, 
    rw_lhss: lean_obj_arg, 
    rw_rhss: lean_obj_arg, 
    rw_dirs: lean_obj_arg,
    optimize_expl: u8,
    gen_nat_lit_rws: u8,
    gen_eta_rw: u8,
    gen_beta_rw: u8,
    viz_path: lean_obj_arg
) -> lean_obj_res {
    let init = lean_string_to_rust(init);
    let goal = lean_string_to_rust(goal);
    let rw_names_c_ptr = lean_array_cptr(rw_names);
    let rw_lhss_c_ptr = lean_array_cptr(rw_lhss);
    let rw_rhss_c_ptr = lean_array_cptr(rw_rhss);
    let rw_dirs_c_ptr = lean_array_cptr(rw_dirs);
    let rws_count = lean_array_size(rw_names);

    unsafe {
        assert_eq!(rws_count, lean_array_size(rw_lhss));
        assert_eq!(rws_count, lean_array_size(rw_rhss));
        assert_eq!(rws_count, lean_array_size(rw_dirs));
    }

    let mut rws : Vec<LeanRewrite> = vec![];
    for idx in 0..(isize::try_from(rws_count).unwrap()) {
        let name                  = lean_string_to_rust(*rw_names_c_ptr.offset(idx));
        let lhs                   = lean_string_to_rust(*rw_lhss_c_ptr.offset(idx));
        let rhs                   = lean_string_to_rust(*rw_rhss_c_ptr.offset(idx));
        let dir: RewriteDirection = lean_unbox(*rw_dirs_c_ptr.offset(idx)).try_into().unwrap();
        
        let new_rws = rewrites_from(name, lhs, rhs, dir);
        if let Err(rws_err) = new_rws { return rust_string_to_lean(rws_err.to_string()) }
        let new_rws = new_rws.unwrap();
        rws.extend(new_rws);
    }
    
    let cfg = Config { 
        optimize_expl:   optimize_expl != 0,  
        gen_nat_lit_rws: gen_nat_lit_rws != 0,  
        gen_eta_rw:      gen_eta_rw != 0,
        gen_beta_rw:     gen_beta_rw != 0  
    };

    let viz_path = lean_string_to_rust(viz_path);
    let viz_path = if viz_path.is_empty() { None } else { Some(viz_path) };

    let expl = explain_congr(init, goal, rws, cfg, viz_path);
    if let Err(expl_err) = expl { return rust_string_to_lean(expl_err.to_string()) }
    let expl = expl.unwrap();
    
    rust_string_to_lean(expl)
}
