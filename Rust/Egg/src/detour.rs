// === minqueue ===

use egg::{Id, EGraph, Language, Extractor, AstSize, FromOp, RecExpr, Rewrite, Subst, ENodeOrVar, PatternAst, CostFunction, Analysis};

use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, BTreeMap};

pub struct MinPrioQueue<U, T>(BinaryHeap<WithOrdRev<U, T>>);

impl<U: Ord, T: Eq> MinPrioQueue<U, T> {
    pub fn new() -> Self {
        MinPrioQueue(BinaryHeap::default())
    }

    pub fn push(&mut self, u: U, t: T) {
        self.0.push(WithOrdRev(u, t));
    }

    pub fn pop(&mut self) -> Option<(U, T)> {
        self.0.pop().map(|WithOrdRev(u, t)| (u, t))
    }
}

// Takes the `Ord` from U, but reverses it.
#[derive(PartialEq, Eq, Debug)]
struct WithOrdRev<U, T>(pub U, pub T);

impl<U: Ord, T: Eq> PartialOrd for WithOrdRev<U, T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // It's the other way around, because we want a min-heap!
        other.0.partial_cmp(&self.0)
    }
}
impl<U: Ord, T: Eq> Ord for WithOrdRev<U, T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(&other).unwrap()
    }
}

// === ctxt cost ===

pub fn compute_ctxt_costs<L: Language, N: Analysis<L>>(root: Id, eg: &EGraph<L, N>, ex: &Extractor<AstSize, L, N>) -> HashMap<Id, usize> {
    let mut ctxt_cost = HashMap::new();

    let mut queue: MinPrioQueue<usize, Id> = MinPrioQueue::new();

    // initial
    queue.push(0, root);

    while let Some((cst, i)) = queue.pop() {
        if ctxt_cost.contains_key(&i) { continue }
        ctxt_cost.insert(i, cst);
        for e in &eg[i].nodes {
            let e_cost = AstSize.cost(e, |k| ex.find_best_cost(k));
            for &c in e.children() {
                // optimization: don't push junk to the queue.
                // NOTE: if we remembered what's the best thing we already pushed to the queue for some class,
                // we could do more efficient pruning.
                if ctxt_cost.contains_key(&c) { continue }

                let c_cost = ex.find_best_cost(c);
                let ncst = e_cost + cst - c_cost;
                queue.push(ncst, c);
            }
        }
    }

    ctxt_cost
}

// === pat detour ===

use std::fmt::Display;

pub fn eqsat_pat_detour<L: Language + Display + FromOp, N: Analysis<L> + Default>(init_term: &str, rws: &[Rewrite<L, N>], stop_size: usize) {
    let st: RecExpr<L> = init_term.parse().unwrap();
    println!("Initial: {st}");
    let mut eg = EGraph::new(Default::default());
    let i = eg.add_expr(&st);

    eg.rebuild();
    for c in 0..520 {
        pat_detour_eqsat_step(c, i, rws, &mut eg);

        let ex = Extractor::new(&eg, AstSize);
        let t = ex.find_best(i);
        println!("Detour Extracted: {}", t.1);
        println!("Total Size: {}", eg.total_size());
        if t.0 <= stop_size { break }
    }
}

pub fn pat_detour_eqsat_step<L: Language + Display, N: Analysis<L>>(c: usize, root: Id, rws: &[Rewrite<L, N>], eg: &mut EGraph<L, N>) {
    let ex = Extractor::new(&eg, AstSize);
    let ctxt_cost = compute_ctxt_costs(root, eg, &ex);

    let mut matches: BTreeMap</*detour cost*/ usize, Vec<(/*rw id*/ usize, Id, Subst, /*ctxt_cost*/ usize, /*pat_cost*/ usize)>> = BTreeMap::default();
    for (rw_i, rw) in rws.iter().enumerate() {
        // to be a bit similar to the backoff scheduler.
        // TODO integrate real backoff scheduler.
/*
        if (&rw.name.to_string() == "ass" || &rw.name.to_string() == "clos") && c % 5 != 0 {
            continue
        }
*/
        let lhs_pat = rw.searcher.get_pattern_ast().unwrap();
        let rhs_pat = rw.applier.get_pattern_ast().unwrap();

        for m in rw.searcher.search(eg) {
            let lhs = m.eclass;
            for subst in m.substs {
                let rhs = lookup_pat(&rhs_pat, eg, &subst);
                if Some(lhs) != rhs {
                    let pat_cost = pat_cost(lhs_pat, &subst, &ex);
                    // We don't subtract the root cost here, it's a constant offset, so why would we.
                    let cx_cost = ctxt_cost[&lhs];
                    let detour_cost = cx_cost + pat_cost;
                    if !matches.contains_key(&detour_cost) {
                        matches.insert(detour_cost, Vec::new());
                    }
                    matches.get_mut(&detour_cost).unwrap().push((rw_i, lhs, subst, cx_cost, pat_cost));
                }
            }
        }
    }

    let Some((full_cost, new_apps)) = matches.into_iter().next() else { return /*saturated*/ };

    let root_cost = ex.find_best_cost(root);
    for (rw_i, lhs, subst, cx_cost, pat_cost) in &new_apps {
        let rw = &rws[*rw_i];

        // Debugging info
        if false {
            // println!("rule \"{}\": {} -> {}", rw.name, rw.searcher.get_pattern_ast().unwrap(), rw.applier.get_pattern_ast().unwrap());
            let ex = Extractor::new(&eg, AstSize);
            println!("cx_cost = {cx_cost:02}, pat_cost = {pat_cost:02}, full_cost = {full_cost:02}, root_cost = {root_cost:02}");
            for v in rw.searcher.vars() {
                let term = ex.find_best(subst[v]).1;
                // println!("  {v} = {term}");
            }
        }

        rw.applier.apply_one(eg, *lhs, subst, None, rw.name);
    }

    eg.rebuild();
}

fn pat_cost<L: Language, N: Analysis<L>>(pat: &PatternAst<L>, subst: &Subst, ex: &Extractor<AstSize, L, N>) -> usize {
    let mut vec: Vec<usize> = Vec::new();
    for i in 0..pat.as_ref().len() {
        let cost = match &pat[i.into()] {
            ENodeOrVar::ENode(n) => AstSize.cost(n, |x| vec[usize::from(x)]),
            ENodeOrVar::Var(v) => ex.find_best_cost(subst[*v]),
        };
        vec.push(cost);
    }
    vec.last().copied().unwrap()
}

// === misc ===

pub fn lookup_pat<L: Language, N: Analysis<L>>(pat: &PatternAst<L>, eg: &EGraph<L, N>, subst: &Subst) -> Option<Id> {
    let mut vec = Vec::new();
    for i in 0..pat.as_ref().len() {
        match &pat[i.into()] {
            ENodeOrVar::ENode(n) => {
                let mut n = n.clone().map_children(|k| vec[usize::from(k)]);
                let k = eg.lookup(&mut n)?;
                vec.push(k);
            },
            ENodeOrVar::Var(v) => vec.push(subst[*v]),
        }
    }
    vec.last().copied()
}
