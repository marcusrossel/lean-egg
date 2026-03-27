use egg::{Id, EGraph, Language, Extractor, AstSize, FromOp, RecExpr, Rewrite, Subst, ENodeOrVar, PatternAst, CostFunction, Analysis, Runner};

use std::fmt::Display;
use std::time::Instant;

pub fn detour_step<L: Language, N: Analysis<L> + Default>(i: usize, roots: &[Id], rws: &[Rewrite<L, N>], eg: &mut EGraph<L, N>, stop: Instant, node_limit: usize) {
    if i%2 == 0 {
        pat_detour_eqsat_step(roots, rws, eg, stop, node_limit);
    } else {
        let egr = std::mem::take(eg);
        let mut runner = Runner::<L, N, ()>::new(N::default())
            .with_egraph(egr)
            .with_iter_limit(1)
            .with_node_limit(node_limit)
            .with_time_limit(stop - Instant::now())
            .run(rws);
        *eg = std::mem::take(&mut runner.egraph);
    }
}

fn pat_detour_eqsat_step<L: Language, N: Analysis<L>>(roots: &[Id], rws: &[Rewrite<L, N>], eg: &mut EGraph<L, N>, stop: Instant, node_limit: usize) {
    let ex = Extractor::new(&eg, AstSize);
    let ctxt_cost = compute_ctxt_costs(roots, eg, &ex);

    let mut matches: BTreeMap</*detour cost*/ usize, Vec<(/*rw id*/ usize, Id, Subst, /*ctxt_cost*/ usize, /*pat_cost*/ usize)>> = BTreeMap::default();
    for (rw_i, rw) in rws.iter().enumerate() {
        let lhs_pat = rw.searcher.get_pattern_ast().unwrap();

        for m in rw.searcher.search(eg) {
            let lhs = m.eclass;
            for subst in m.substs {
                let pat_cost = pat_cost(lhs_pat, &subst, &ex);
                // We don't subtract the root cost here, it's a constant offset, so why would we.
                let cx_cost = *ctxt_cost.get(&lhs).unwrap_or(&100000000); // this is the cost you get from not being able to reach any root.
                let detour_cost = cx_cost + pat_cost;
                if !matches.contains_key(&detour_cost) {
                    matches.insert(detour_cost, Vec::new());
                }
                matches.get_mut(&detour_cost).unwrap().push((rw_i, lhs, subst, cx_cost, pat_cost));
                if Instant::now() > stop { return }
            }
        }
    }

    let eg_data = |eg: &EGraph<_, _>| (eg.number_of_classes(), eg.total_size());

    let og_data = eg_data(eg);
    let mut found_cost = None;

    const OFFSET: usize = 3;

    'outer: for (full_cost, new_apps) in matches {
        if let Some(found) = found_cost { if full_cost > found + OFFSET { break } }
        for (rw_i, lhs, subst, cx_cost, pat_cost) in &new_apps {
            let rw = &rws[*rw_i];
            let pat_ast = rw.searcher.get_pattern_ast();
            rw.applier.apply_one(eg, *lhs, subst, pat_ast, rw.name);
            if eg_data(eg) != og_data { found_cost = Some(full_cost); }
            if Instant::now() > stop { break 'outer }
            if eg.total_size() > node_limit { break 'outer }
        }
    }

    eg.rebuild();
}

// === ctxt cost ===

fn compute_ctxt_costs<L: Language, N: Analysis<L>>(roots: &[Id], eg: &EGraph<L, N>, ex: &Extractor<AstSize, L, N>) -> HashMap<Id, usize> {
    let mut ctxt_cost = HashMap::new();

    let mut queue: MinPrioQueue<usize, Id> = MinPrioQueue::new();

    // initial
    for root in roots {
        queue.push(0, *root);
    }

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

fn lookup_pat<L: Language, N: Analysis<L>>(pat: &PatternAst<L>, eg: &EGraph<L, N>, subst: &Subst) -> Option<Id> {
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


// === minqueue ===

use std::cmp::Ordering;
use std::collections::{BinaryHeap, HashMap, BTreeMap};

struct MinPrioQueue<U, T>(BinaryHeap<WithOrdRev<U, T>>);

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

