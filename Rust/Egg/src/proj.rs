use std::collections::HashMap;
use egg::*;
use crate::analysis::*;
use crate::lean_expr::*;

#[derive(Clone)]
pub struct StructInfo {
    pub params: usize,
    pub fields: usize
}

impl StructInfo {

    fn pattern(&self, struct_name: &str) -> (Pattern<LeanExpr>, Vec<Var>) {
        let mut pat = format!("(mk \"{}\" ?l)", struct_name).to_string();
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

    fn apply_one(&self, graph: &mut LeanEGraph, id: Id, subst: &Subst, ast: Option<&PatternAst<LeanExpr>>, rule: Symbol) -> Vec<Id> {
        use std::fs::OpenOptions;
        use std::io::prelude::*;
        let mut file = OpenOptions::new().write(true).append(true).open("/Users/marcus/Desktop/dot/log.txt").unwrap();
        let _ = writeln!(file, "start {}", rule);
        
        let Some(LeanExpr::Str(struct_name)) = graph[subst[self.struct_name]].nodes.first() else { return vec![] };
        let Some(info) = self.struct_info.get(struct_name) else { return vec![] };
        let Some(LeanExpr::Nat(proj_idx)) = graph[subst[self.proj_idx]].nodes.first() else { return vec![] };
        let (struct_val_pat, field_vars) = info.pattern(struct_name);
        let field_var = field_vars[*proj_idx as usize];

        // TODO: This is a hacky way of combining `ast` with `struct_val_pat`. Is there a nicer way?
        let complete_pat: Pattern<_> = ast.unwrap().to_string().replace( 
            &self.struct_val.to_string(), 
            &struct_val_pat.to_string()
        ).parse().unwrap();

        // TODO: It would be more efficient to only search the `struct_val_id` e-class with the 
        //       `struct_val_pat`, instead of repeating the search of the outer pattern as part of
        //       `complete_pat`. The only problem with this is that the resulting subst from the 
        //       "inner" search would have to be combined with the subst from the "outer" search, 
        //       and currently does not have an API for this.
        //
        // let struct_val_id = subst[self.struct_val];
        // graph.rebuild();
        // let Some(struct_vals) = struct_val_pat.search_eclass(graph, struct_val_id) else { return vec![] };
        // let mut changed = vec![];
        // for inner_subst in struct_vals.substs {
        //     let complete_subst = inner_subst.merge(subst);
        //     let field_pat = RecExpr::from(vec![ENodeOrVar::Var(field_var)]);
        //     let (i, did_change) = graph.union_instantiations(&complete_pat, &field_pat, &complete_subst, rule);
        //     if did_change { changed.push(i); }
        // }
        graph.rebuild();
        let _ = writeln!(file, "after rebuild: {complete_pat}");
        let Some(matches) = complete_pat.search_eclass(graph, id) else { 
            let _ = writeln!(file, "no match");
            return vec![] 
        };
        let _ = writeln!(file, "match");

        let mut changed = vec![];
        for subst in matches.substs {
            let field_pat = RecExpr::from(vec![ENodeOrVar::Var(field_var)]);
            let (i, did_change) = graph.union_instantiations(&complete_pat.ast, &field_pat, &subst, rule);
            if did_change {
                changed.push(i);
            }
        }
        changed
    }
}

fn proj_rw(params: usize, struct_info : HashMap<String, StructInfo>) -> LeanRewrite {
    // TODO: Do the universe levels of the projection really have to match the levels of the ctor?
    //       Because if not, the name `?l` might clash with the name chosen in `StructInfo.pattern`.
    let mut outer_pat = "(proj ?S ?idx ?l)".to_string();
    for idx in 0..params {
        outer_pat = format!("(app {} ?o{})", outer_pat, idx);
    }
    outer_pat = format!("(app {} ?s)", outer_pat);
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