use crate::analysis::*;
use crate::Symbol;
use crate::egraph::{id_to_expr, RuleTable};
use crate::proof::*;
use crate::util::*;
use crate::LeanExpr;
use std::collections::{HashMap, HashSet};
use std::panic::AssertUnwindSafe;
use std::rc::Rc;
use rs2::{Analysis, Id};

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
    egraph: &LeanEGraph, rules: &RuleTable, enodes: &[LeanExpr], init_expr: LeanTerm, goal_expr: LeanTerm,
    init_id: PId, goal_id: PId
) -> (ExplanationKind, String) {
    let (init, goal) = (init_id.clone(), goal_id.clone());
    match ExplanationKind::for_goal(egraph, init_expr, goal_expr, init_id, goal_id) {
        None => (ExplanationKind::None, "".to_string()),
        // Note: We catch panics, as they would otherwise abort the Lean process (panics cannot
        //       unwind across the FFI boundary).
        Some((kind, lhs, rhs)) => match std::panic::catch_unwind(AssertUnwindSafe(|| {
            // The ids with which the goal's terms were created represent them exactly, so we use
            // them instead of looking up the terms again (which can introduce detours).
            let ids = match kind {
                ExplanationKind::SameEClass => Some((init, goal)),
                ExplanationKind::EqTrue     => egraph.lookup(&LeanExpr::Eq([init, goal])).zip(egraph.lookup_term(&rhs)),
                ExplanationKind::None       => None,
            };
            explain_equivalence(egraph, rules, enodes, &lhs, &rhs, ids)
        })) {
            Ok(Ok(expl)) => (kind, expl),
            Ok(Err(msg)) => (ExplanationKind::None, msg),
            Err(panic)   => (ExplanationKind::None, format!("GUF explanation failed: {}", panic_msg(&panic)))
        }
    }
}

fn panic_msg(panic: &Box<dyn std::any::Any + Send>) -> String {
    if let Some(msg) = panic.downcast_ref::<&str>() { msg.to_string() }
    else if let Some(msg) = panic.downcast_ref::<String>() { msg.clone() }
    else { "unknown panic".to_string() }
}

// Analogous to `explain_equivalence(lhs, rhs).get_flat_string()` in egg.
// The `rules` map the ids in `ProofObj::Rule` to the corresponding rule applications, and `enodes`
// are the e-nodes with which the e-graph's e-classes were created (cf. `id_to_expr`). If given,
// `ids` are proof-annotated e-class ids representing exactly `lhs` and `rhs`.
fn explain_equivalence(egraph: &LeanEGraph, rules: &RuleTable, enodes: &[LeanExpr], lhs: &LeanTerm, rhs: &LeanTerm, ids: Option<(PId, PId)>) -> Result<String, String> {
    // Like egg, we explain syntactically equal terms without any steps.
    if lhs == rhs { return Ok(format!("{}\n", stringify_term(lhs, None))) }

    note("explain_equiv!");
    let (lhs_id, rhs_id) = ids.unwrap_or_else(|| (egraph.lookup_term(lhs).unwrap(), egraph.lookup_term(rhs).unwrap()));
    // The proof `p` with `p * lhs_id = rhs_id`, that is, a proof of `lhs = rhs`.
    let proof = egraph.get_g_between(lhs_id, rhs_id).unwrap();

    let mut terms = Terms { enodes, cache: HashMap::new() };

    // As rule steps are ground (cf. `RuleApplication`), we can evaluate the proof forwards from
    // `lhs`. We only fall back to the unification-based evaluation if that fails, which would happen
    // if a rule application lacked the terms of some of its variables.
    let e = match eval_forward(&proof, lhs, rhs, rules, &mut terms) {
        Ok(e) => e,
        Err(msg) => {
            note(&format!("forward evaluation failed: {msg}"));
            eval_by_unification(&proof, lhs, rhs, rules, &mut terms)
        }
    };

    note("pre-guess!");
    let e = guess_mvars(e);

    note("pre-stringify!");
    let stringified = stringify(&e);
    note(&format!("stringified:\n{stringified}\n"));

    Ok(stringified)
}

fn eval_by_unification(proof: &Proof, lhs: &LeanTerm, rhs: &LeanTerm, rules: &RuleTable, terms: &mut Terms) -> Expl {
    let mut mvar_counter = 0;
    let mut umap = UnifyMap::default();

    note("pre-eval!");
    let mut e = eval(proof, &mut mvar_counter, &mut umap, rules, terms);

    note("pre-unify!");
    unify(e.first(), &explify(lhs), &mut umap);
    unify(&e.last, &explify(rhs), &mut umap);

    note("pre-canon!");
    for t in e.all_terms() {
        *t = umap_canon(t, &umap);
    }

    remove_cycles(e)
}

// Evaluates the given proof of `lhs = rhs` by applying its steps to `lhs`. This requires all rule
// steps to be ground. The resulting explanation contains no detours (cf. `ExplBuilder`).
fn eval_forward(proof: &Proof, lhs: &LeanTerm, rhs: &LeanTerm, rules: &RuleTable, terms: &mut Terms) -> Result<Expl, String> {
    let mut fwd = Forward { rules, terms, ground: HashMap::new(), path: Vec::new(), steps: Vec::new() };
    let end = fwd.eval(proof, lhs.clone(), true)?;
    if end != *rhs { return Err(format!("the proof ends in {end:?} instead of {rhs:?}")) }

    // Replays the steps on `lhs` to obtain the entire term after each step.
    let mut cur = lhs.clone();
    let mut expl = ExplBuilder::new(cur.clone());
    for (path, step, result) in fwd.steps {
        *subterm_mut(&mut cur, &path) = result;
        expl.push(step, cur.clone());
    }
    Ok(expl.finish())
}

// The state of `eval_forward`.
struct Forward<'a, 'b> {
    rules:  &'a RuleTable,
    terms:  &'a mut Terms<'b>,
    // The instantiated `lhs` and `rhs` of each rule application encountered so far.
    ground: HashMap<RuleId, (LeanTerm, LeanTerm)>,
    // The position of the subterm currently being evaluated (outermost index first).
    path:   Vec<usize>,
    // The steps performed so far, each with the position it applies to and the resulting subterm.
    steps:  Vec<(Vec<usize>, ExplStep, LeanTerm)>,
}

impl Forward<'_, '_> {

    // Applies `p` (or `p⁻¹` if `!fwd`) to the term `t` at position `self.path`, and returns the
    // resulting term.
    fn eval(&mut self, p: &Proof, t: LeanTerm, fwd: bool) -> Result<LeanTerm, String> {
        match &*p.0 {
            ProofObj::Refl => Ok(t),
            ProofObj::Sym(q) => self.eval(q, t, !fwd),
            // `Trans(p2, p1)` first applies `p1`, then `p2`.
            ProofObj::Trans(p2, p1) => if fwd {
                let t = self.eval(p1, t, true)?;
                self.eval(p2, t, true)
            } else {
                let t = self.eval(p2, t, false)?;
                self.eval(p1, t, false)
            },
            ProofObj::Congr(sid, children) => {
                let LeanPattern::Node(node, args) = t else { return Err(format!("congruence on {t:?}")) };
                if SymbolId::from_enode(&node) != *sid || args.len() != children.len() {
                    return Err(format!("congruence proof does not apply to {node:?}"))
                }
                let mut new_args = Vec::with_capacity(args.len());
                for (i, (arg, child)) in args.into_vec().into_iter().zip(children.iter()).enumerate() {
                    self.path.push(i);
                    new_args.push(self.eval(child, arg, fwd)?);
                    self.path.pop();
                }
                Ok(LeanPattern::Node(node, new_args.into()))
            },
            ProofObj::Rule(id) => {
                let (lhs, rhs) = self.ground(*id);
                let (from, to) = if fwd { (lhs, rhs) } else { (rhs, lhs) };
                let rule = self.rules.get(*id).name.clone();
                // The rule's patterns are ground, unless a variable's term was not recorded.
                let mut bindings = UnifyMap::default();
                if !match_pattern(&from, &t, &mut bindings) {
                    return Err(format!("rule {rule} does not apply to {t:?}"))
                }
                let result = umap_canon(&to, &bindings);
                if !is_ground(&result) { return Err(format!("rule {rule} yields non-ground {result:?}")) }
                let pos = self.path.iter().rev().copied().collect();
                self.steps.push((self.path.clone(), ExplStep { rule, forward: fwd, pos }, result.clone()));
                Ok(result)
            },
        }
    }

    // The `lhs` and `rhs` of the given rule application, instantiated with its substitution.
    fn ground(&mut self, id: RuleId) -> (LeanTerm, LeanTerm) {
        if let Some(sides) = self.ground.get(&id) { return sides.clone() }
        let entry = self.rules.get(id);
        let subst: UnifyMap = self.rules.subst(id).iter().map(|(var, x)| (*var, self.terms.get(*x))).collect();
        let sides = (umap_canon(&entry.lhs, &subst), umap_canon(&entry.rhs, &subst));
        self.ground.insert(id, sides.clone());
        sides
    }
}

// Matches `pat` against `t`, extending `bindings` with the pattern's variables.
fn match_pattern(pat: &LeanPattern, t: &LeanTerm, bindings: &mut UnifyMap) -> bool {
    match (pat, t) {
        (LeanPattern::PVar(var), _) => match bindings.get(var) {
            Some(bound) => bound == t,
            None        => { bindings.insert(*var, t.clone()); true }
        },
        (LeanPattern::Node(n1, ps), LeanPattern::Node(n2, ts)) =>
            LeanAnalysis::matches(n1, n2) && ps.len() == ts.len() &&
            ps.iter().zip(ts.iter()).all(|(p, t)| match_pattern(p, t, bindings)),
        _ => false,
    }
}

fn is_ground(t: &LeanPattern) -> bool {
    match t {
        LeanPattern::PVar(_)           => false,
        LeanPattern::Node(_, children) => children.iter().all(is_ground),
        LeanPattern::G(..)             => unreachable!(),
    }
}

fn subterm_mut<'a>(t: &'a mut LeanPattern, path: &[usize]) -> &'a mut LeanPattern {
    match (path.split_first(), t) {
        (None, t) => t,
        (Some((i, rest)), LeanPattern::Node(_, children)) => subterm_mut(&mut children[*i], rest),
        _ => unreachable!("invalid position"),
    }
}

struct Expl {
    vec: Vec<(LeanPattern, ExplStep)>,
    last: LeanPattern,
}

// Builds an explanation step by step while removing detours: if a term occurs again, we drop all
// steps since its previous occurrence.
struct ExplBuilder {
    // Each term of the explanation together with the step from it to the next term (if any).
    terms: Vec<(LeanPattern, Option<ExplStep>)>,
    idx:   HashMap<LeanPattern, usize>,
}

impl ExplBuilder {

    fn new(first: LeanPattern) -> Self {
        let idx = HashMap::from([(first.clone(), 0)]);
        ExplBuilder { terms: vec![(first, None)], idx }
    }

    // Adds the given step, which leads from the last term of the explanation to `term`.
    fn push(&mut self, step: ExplStep, term: LeanPattern) {
        if let Some(&i) = self.idx.get(&term) {
            for (dropped, _) in self.terms.drain(i + 1..) { self.idx.remove(&dropped); }
            self.terms[i].1 = None;
        } else {
            self.terms.last_mut().unwrap().1 = Some(step);
            self.idx.insert(term.clone(), self.terms.len());
            self.terms.push((term, None));
        }
    }

    fn finish(mut self) -> Expl {
        let (last, _) = self.terms.pop().unwrap();
        Expl { vec: self.terms.into_iter().map(|(t, step)| (t, step.unwrap())).collect(), last }
    }
}

// Removes detours from the given explanation (cf. `ExplBuilder`).
fn remove_cycles(e: Expl) -> Expl {
    let Expl { vec, last } = e;
    let mut steps = vec.into_iter();
    let Some((first, mut step)) = steps.next() else { return Expl { vec: Vec::new(), last } };
    let mut expl = ExplBuilder::new(first);
    for (term, next) in steps {
        expl.push(step, term);
        step = next;
    }
    expl.push(step, last);
    expl.finish()
}

// The terms of e-classes (cf. `id_to_expr`), which are computed on demand.
struct Terms<'a> {
    enodes: &'a [LeanExpr],
    cache:  HashMap<Id, LeanTerm>,
}

impl Terms<'_> {
    fn get(&mut self, id: Id) -> LeanTerm {
        let enodes = self.enodes;
        self.cache.entry(id).or_insert_with(|| id_to_expr(enodes, id)).clone()
    }
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
        (LeanPattern::PVar(p1), LeanPattern::PVar(p2)) if p1 == p2 => {},
        (LeanPattern::PVar(p), t)|(t, LeanPattern::PVar(p)) => {
            assert!(!contains_var(&t, p));
            // Note: We don't need to resolve the other bindings, as `umap_canon` follows bindings.
            umap.insert(p, t.clone());
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

fn eval(p: &Proof, mvar_counter: &mut usize, umap: &mut UnifyMap, rules: &RuleTable, terms: &mut Terms) -> Expl {
    match &*p.0 {
        ProofObj::Refl => Expl {
            vec: Vec::new(),
            last: LeanPattern::PVar(fresh_mvar(mvar_counter)),
        },
        ProofObj::Sym(p) => {
            let e = eval(p, mvar_counter, umap, rules, terms);
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
            let e1 = eval(p1, mvar_counter, umap, rules, terms);
            let e2 = eval(p2, mvar_counter, umap, rules, terms);
            eval_trans(e2, e1, umap)
        },
        ProofObj::Congr(sid, children) => {
            let mut cs = Vec::new();
            for (i, c) in children.iter().enumerate() {
                let inner = eval(c, mvar_counter, umap, rules, terms);
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

            // We instantiate the rule's variables with the terms they were instantiated with when
            // the rule was applied. Thus, only unrecorded variables (if any) become mvars.
            let subst: UnifyMap = rules.subst(*rule_id).iter().map(|(var, id)| (*var, terms.get(*id))).collect();
            let mut lhs = umap_canon(&entry.lhs, &subst);
            let mut rhs = umap_canon(&entry.rhs, &subst);
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
            let name = symbolic_expressions::encode_string(&step_.rule);
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
