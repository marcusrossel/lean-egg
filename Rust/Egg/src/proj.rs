use std::collections::HashMap;
use egg::*;
use crate::analysis::*;
use crate::lean_expr::*;

#[derive(Clone)]
pub struct StructInfo {
    pub params: usize,
    pub fields: usize,
    pub levels: usize
}

impl StructInfo {

    fn pattern(&self, struct_name: &str) -> (Pattern<LeanExpr>, Vec<Var>) {
        let mut levels = "".to_string();
        for i in 0..self.levels { levels += &format!(" ?u{}", i) }

        let mut pat = format!("(mk \"{}\"{})", struct_name, levels).to_string();
        for i in 0..self.params { pat = format!("(app {} ?p{})", pat, i) }
        
        let mut field_vars = vec![];
        for i in 0..self.fields { 
            let var = format!("?f{}", i).parse().unwrap();
            pat = format!("(app {} {})", pat, var);
            field_vars.push(var);
        }
        
        (pat.parse().unwrap(), field_vars)
    }
}

struct ProjApplier {
    pub struct_name: Var,
    pub proj_idx: Var,
    pub struct_val: Var,
    pub struct_info: HashMap<String, StructInfo>,
}

impl Applier<LeanExpr, LeanAnalysis> for ProjApplier {

    fn apply_one(&self, graph: &mut LeanEGraph, _: Id, subst: &Subst, _: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        let Some(LeanExpr::Str(struct_name)) = graph[subst[self.struct_name]].nodes.first() else { return vec![] };
        let Some(info) = self.struct_info.get(struct_name) else { return vec![] };
        let Some(LeanExpr::Nat(proj_idx)) = graph[subst[self.proj_idx]].nodes.first() else { return vec![] };
        let struct_val_id = subst[self.struct_val];
        let struct_val_pat = info.pattern(struct_name);
        todo!()
    }
}

fn proj_rw(params: usize, struct_info : HashMap<String, StructInfo>) -> LeanRewrite {
    let mut outer_pat = "(app (proj ?S ?idx) ?s)".to_string();
    for idx in 0..params {
        outer_pat = format!("(app {} ?o{})", outer_pat, idx);
    }
    let outer_pat: Pattern<_> = outer_pat.parse().unwrap();
    
    let applier = ProjApplier { 
        struct_name: "?S".parse().unwrap(), 
        proj_idx: "?idx".parse().unwrap(),
        struct_val: "?s".parse().unwrap(),
        struct_info: struct_info
    };
    
    Rewrite::new(format!("≡proj<{}>", params), outer_pat, applier).unwrap()
}

pub fn proj_rws(struct_info : HashMap<String, StructInfo>) -> Vec<LeanRewrite> {
    let mut params: Vec<_> = struct_info.values().map(|i| i.params).collect();
    params.sort();
    params.dedup();

    let mut rws = vec![];
    for p in params {
        rws.push(proj_rw(p, struct_info.clone()));
    }   
    rws
}