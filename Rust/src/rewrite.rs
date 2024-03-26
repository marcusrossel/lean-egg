use egg::*;
use crate::result::*;
use crate::lean_expr::*;
use crate::analysis::*;
use crate::bvar_capture::*;

pub struct RewriteTemplate {
    pub name: String,
    pub lhs: Pattern<LeanExpr>,
    pub rhs: Pattern<LeanExpr>
}

pub fn templates_to_rewrites(templates: Vec<RewriteTemplate>, block_invalid_matches: bool, shift_captured_bvars: bool) -> Res<Vec<LeanRewrite>> {
    let mut result: Vec<LeanRewrite> = vec![];
    for template in templates {
        let rw = if shift_captured_bvars || block_invalid_matches { 
            let applier = BVarCapture { rhs: template.rhs, block_invalid_matches: block_invalid_matches, shift_captured_bvars: shift_captured_bvars };
            Rewrite::new(template.name, template.lhs, applier)
        } else { 
            Rewrite::new(template.name, template.lhs, template.rhs) 
        };
        match rw {
            Ok(r) => result.push(r),
            Err(err) => return Err(Error::Rewrite(err.to_string()))
        }
    }
    Ok(result)
}