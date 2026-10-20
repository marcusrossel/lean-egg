use crate::analysis::*;
use crate::Symbol;
use crate::egraph::RuleTable;
use crate::proof::*;
use crate::util::*;
use crate::LeanExpr;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use rs2::Analysis;

#[derive(Clone, Copy)]
pub enum ExplanationKind {
    None,
    SameEClass,
    EqTrue
}

impl ExplanationKind {
    pub fn to_c(self) -> u8 {
        match self {
            Self::None => 0,
            Self::SameEClass => 1,
            Self::EqTrue => 2,
        }
    }

    fn for_goal(
        egraph: &LeanEGraph, init_expr: LeanTerm, goal_expr: LeanTerm, init_id: PId, goal_id: PId
    ) -> Option<(ExplanationKind, LeanTerm, LeanTerm)> {
        if egraph.find(init_id).1 == egraph.find(goal_id).1 {
            return Some((ExplanationKind::SameEClass, init_expr, goal_expr))
        }

        let eq_expr = term(&format!("(= {:?} {:?})", init_expr, goal_expr));
        let true_expr = term("(const \"True\")");
        let true_id = egraph.lookup_term(&true_expr).unwrap();

        // Note: `lookup_term` does not necessarily return canonical ids.
        if egraph.lookup_term(&eq_expr).map(|x| egraph.find(x).1) == Some(egraph.find(true_id).1) {
            return Some((ExplanationKind::EqTrue, eq_expr, true_expr))
        }

        None
    }
}

pub fn mk_explanation(
    egraph: &LeanEGraph, rules: &RuleTable, init_expr: LeanTerm, goal_expr: LeanTerm, init_id: PId, goal_id: PId
) -> (ExplanationKind, String) {
    match ExplanationKind::for_goal(egraph, init_expr, goal_expr, init_id, goal_id) {
        None => (ExplanationKind::None, "".to_string()),
        Some((kind, lhs, rhs)) => match explain_equivalence(egraph, rules, &lhs, &rhs) {
            Ok(expl) => (kind, expl),
            Err(msg) => (ExplanationKind::None, msg)
        }
    }
}

// Analogous to `explain_equivalence(lhs, rhs).get_flat_string()` in egg.
// The `rules` map the ids in `ProofObj::Rule` to the corresponding rule names and patterns.
fn explain_equivalence(egraph: &LeanEGraph, rules: &RuleTable, lhs: &LeanTerm, rhs: &LeanTerm) -> Result<String, String> {
    note("explain_equiv!");
    let lhs_id = egraph.lookup_term(lhs).unwrap();
    let rhs_id = egraph.lookup_term(rhs).unwrap();
    // The proof `p` with `p * lhs_id = rhs_id`, that is, a proof of `lhs = rhs`.
    let proof = egraph.get_g_between(lhs_id, rhs_id).unwrap();

    let mut mvar_counter = 0;
    let mut umap = UnifyMap::default();

    note("pre-psize!");

    let psize = psize_fast(&proof, &mut Default::default());
    if psize > 1000 { return Err("proof too big".to_string()) }

    note("pre-eval!");

    note(&format!("eval({})", psize));
    let mut e = eval(&proof, &mut mvar_counter, &mut umap, rules);

    note("pre-unify!");
    unify(e.first(), &explify(lhs), &mut umap);
    unify(&e.last, &explify(rhs), &mut umap);

    note("pre-canon!");
    for t in e.all_terms() {
        *t = umap_canon(t, &umap);
    }

    note("pre-guess!");
    let e = guess_mvars(e);

    note("pre-stringify!");
    let stringified = stringify(&e);
    note(&format!("stringified:\n{stringified}\n"));

    Ok(stringified)
}

struct Expl {
    vec: Vec<(LeanPattern, ExplStep)>,
    last: LeanPattern,
}

impl Expl {
    pub fn first(&self) -> &LeanPattern {
        self.vec.first().map(|(x, _)| x).unwrap_or_else(|| &self.last)
    }

    pub fn all_terms(&mut self) -> impl Iterator<Item=&mut LeanPattern> {
        self.vec.iter_mut().map(|(x, _)| x).chain(std::iter::once(&mut self.last))
    }
}

#[derive(Clone)]
struct ExplStep {
    rule: Rc<str>,
    forward: bool,
    pos: Vec<usize>,
}

type UnifyMap = HashMap<Symbol, LeanPattern>;

fn umap_canon(t: &LeanPattern, umap: &UnifyMap) -> LeanPattern {
    match t {
        LeanPattern::PVar(p) => match umap.get(p) {
            Some(t) => umap_canon(t, umap),
            None => LeanPattern::PVar(*p),
        }
        LeanPattern::Node(n, children) => {
            LeanPattern::Node(n.clone(),
                children.iter().map(|x| umap_canon(x, umap)).collect()
            )
        },
        LeanPattern::G(..) => unreachable!(),
    }
}

fn contains_var(p: &LeanPattern, v: Symbol) -> bool {
    match p {
        LeanPattern::PVar(v2) => v == *v2,
        LeanPattern::Node(_, children) => children.iter().any(|c| contains_var(c, v)),
        LeanPattern::G(..) => unreachable!(),
    }
}

// will panic if it can't unify.
fn unify(l: &LeanPattern, r: &LeanPattern, umap: &mut UnifyMap) {
    let l = umap_canon(l, umap);
    let r = umap_canon(r, umap);
    match (l, r) {
        (LeanPattern::PVar(p), t)|(t, LeanPattern::PVar(p)) => {
            assert!(!contains_var(&t, p));
            umap.insert(p, t.clone());
            *umap = umap.iter().map(|(k, v)| (*k, umap_canon(v, umap))).collect();
        },
        (LeanPattern::Node(n1, cs1), LeanPattern::Node(n2, cs2)) => {
            assert!(LeanAnalysis::matches(&n1, &n2), "{n1:?} ~!~ {n2:?}");
            for (c1, c2) in cs1.iter().zip(cs2.iter()) {
                unify(c1, c2, umap);
            }
        },
        (LeanPattern::G(..),_)|(_,LeanPattern::G(..)) => unreachable!(),
    }
}

fn eval_trans(e2: Expl, e1: Expl, umap: &mut UnifyMap) -> Expl {
    let ll = umap_canon(&e1.last, umap);
    let rr = umap_canon(e2.first(), umap);

    note(&format!("trans unify: {ll:?} ~ {rr:?}"));
    unify(&ll, &rr, umap);
    note("trans unify success!");

    Expl {
        vec: e1.vec.iter().cloned().chain(e2.vec.iter().cloned()).collect(),
        last: e2.last.clone(),
    }
}

fn psize_fast(p: &Proof, things: &mut HashMap<*const ProofObj, usize>) -> usize {
    let pp = &*p.0 as *const ProofObj;

    if let Some(x) = things.get(&pp) { return *x }

    let v = match &*p.0 {
        ProofObj::Refl => 1,
        ProofObj::Sym(p) => psize_fast(p, things) + 1,
        ProofObj::Trans(p1, p2) => psize_fast(p1, things) + psize_fast(p2, things) + 1,
        ProofObj::Congr(_, children) => children.iter().map(|ii| psize_fast(ii, things)).sum::<usize>() + 1,
        ProofObj::Rule(_) => 1,
    };
    things.insert(pp, v);
    v
}

fn eval(p: &Proof, mvar_counter: &mut usize, umap: &mut UnifyMap, rules: &RuleTable) -> Expl {
    match &*p.0 {
        ProofObj::Refl => Expl {
            vec: Vec::new(),
            last: LeanPattern::PVar(fresh_mvar(mvar_counter)),
        },
        ProofObj::Sym(p) => {
            let e = eval(p, mvar_counter, umap, rules);
            let n = e.vec.len();
            Expl {
                vec: (0..n).rev().map(|i| {
                    let node = if i == n-1 { &e.last } else { &e.vec[i+1].0 }.clone();
                    let mut edge = e.vec[i].1.clone();
                    edge.forward = !edge.forward;
                    (node, edge)
                }).collect(),
                last: e.first().clone(),
            }
        },
        ProofObj::Trans(p2, p1) => {
            let e1 = eval(p1, mvar_counter, umap, rules);
            let e2 = eval(p2, mvar_counter, umap, rules);
            eval_trans(e2, e1, umap)
        },
        ProofObj::Congr(sid, children) => {
            let mut cs = Vec::new();
            for (i, c) in children.iter().enumerate() {
                let inner = eval(c, mvar_counter, umap, rules);
                let wrapped = wrap(inner, mvar_counter, i, children.len(), *sid);
                cs.push(wrapped);
            }
            let mut total = cs.pop().unwrap();
            for x in cs.into_iter().rev() {
                total = eval_trans(x, total, umap);
            }
            total
        },
        ProofObj::Rule(rule_id) => {
            let entry = rules.get(*rule_id).clone();
            let step = ExplStep { rule: entry.name, forward: true, pos: Vec::new() };

            let mut lhs = entry.lhs;
            let mut rhs = entry.rhs;
            let mut map = HashMap::new();
            refresh_mvars(&mut lhs, mvar_counter, &mut map);
            refresh_mvars(&mut rhs, mvar_counter, &mut map);

            Expl {
                vec: vec![(lhs, step)],
                last: rhs,
            }
        },
    }
}

fn wrap(mut e: Expl, mvar_counter: &mut usize, i: usize, arity: usize, si: SymbolId) -> Expl {
    let l: Box<[LeanPattern]> = (0..arity).map(|_| LeanPattern::PVar(fresh_mvar(mvar_counter))).collect();
    for p in e.vec.iter_mut().map(|(_, step)| &mut step.pos) {
        p.push(i);
    }
    for t in e.all_terms() {
        let node = si.build(vec![nil(); arity].into());
        let mut children = l.clone();
        children[i] = t.clone();
        *t = LeanTerm::Node(node, children);
    }
    e
}

fn fresh_mvar(mvar_counter: &mut usize) -> Symbol {
    let x = *mvar_counter;
    *mvar_counter += 1;
    Symbol::from(format!("fresh{x}"))
}

fn refresh_mvars(t: &mut LeanPattern, mvar_counter: &mut usize, map: &mut HashMap<Symbol, Symbol>) {
    match t {
        LeanPattern::PVar(v) => {
            let vv = if let Some(vv) = map.get(v) { *vv } else {
                let vv = fresh_mvar(mvar_counter);
                map.insert(*v, vv);
                vv
            };
            *t = LeanPattern::PVar(vv);
        },
        LeanPattern::Node(n, children) => {
            for c in children {
                refresh_mvars(c, mvar_counter, map);
            }
        },
        LeanPattern::G(..) => unreachable!(),
    }
}

// remove all remaining mvars by instantiating them with some guessed value.
fn guess_mvars(expl: Expl) -> Expl {
    // TODO actually do that
    expl
}

fn explify(l: &LeanTerm) -> LeanPattern {
    l.clone()
}

fn stringify(e: &Expl) -> String {
    let mut out = String::new();

    out.push_str(&stringify_term(e.first(), None));
    out.push('\n');

    for i in 0..e.vec.len() {
        let s = e.vec[i].1.clone();
        let t = if i == e.vec.len()-1 { &e.last } else { &e.vec[i+1].0 };
        out.push_str(&stringify_term(t, Some(s)));
        out.push('\n');
    }

    out
}

fn stringify_term(t: &LeanPattern, step: Option<ExplStep>) -> String {
    if let Some(step_) = &step {
        if step_.pos.is_empty() {
            let subterm = stringify_term(t, None);
            let dir = if step_.forward { "=>" } else { "<=" };
            let name = &step_.rule;
            return format!("(Rewrite{dir} {name} {subterm})")
        }
    }

    match t {
        LeanPattern::Node(n, children) => {
            let op = symbolic_expressions::encode_string(&n.op());
            let child_strings: Vec<String> = children.iter().enumerate().map(|(j, x)| {
                if let Some(step_) = &step {
                    if Some(j) == step_.pos.last().copied() {
                        let mut step2 = step_.clone();
                        step2.pos.pop();
                        return stringify_term(x, Some(step2))
                    }
                }
                return stringify_term(x, None)
            }).collect();
            if n.is_leaf() {
                op
            } else {
                format!("({} {})", op, child_strings.join(" "))
            }
        },
        LeanPattern::PVar(v) => format!("?{v}"),
        LeanPattern::G(..) => unreachable!(),
    }
}



use std::fs::OpenOptions;
use std::io::{self, Write};
use std::path::PathBuf;

fn note(text: &str) {
    let mut path = PathBuf::from(std::env::var("HOME").map_err(|_| {
        io::Error::new(io::ErrorKind::NotFound, "HOME environment variable not set")
    }).unwrap());
    path.push("log");

    let mut file = OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
        .unwrap();

    writeln!(file, "{}", text).unwrap();
}
