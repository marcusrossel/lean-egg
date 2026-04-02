use egg::{Id, EGraph, Language, Extractor, FromOp, RecExpr, Rewrite, Subst, ENodeOrVar, PatternAst, CostFunction, Analysis, Runner, Report, StopReason, BackoffScheduler, SimpleScheduler, RewriteScheduler, SearchMatches};

use std::fmt::Display;
use std::time::{Duration, Instant};

pub type Hook<L, N> = Box<dyn FnMut(&mut EGraph<L, N>) -> Result<(), String>>;
type RewriteId = usize;
type Cost = u128;

// note: 'cf: fn(&L) -> Cost' will ignore the costs of the children!
pub fn detour_run<L: Language, N: Analysis<L> + Default>(roots: &[Id], rws: &[Rewrite<L, N>], eg: &mut EGraph<L, N>, hooks: &mut [Hook<L, N>], time_limit: Duration, node_limit: usize, cf: fn(&L) -> Cost, cfg_offset: Cost, cfg_unreachable_cost: Cost) -> Report {
    let mut stop_reason = StopReason::Saturated;

    let start = Instant::now();

    let stopper = Stopper {
        start,
        time_limit,
        node_limit
    };

    let mut sched = BackoffScheduler::default();

    // The initial e-graph might be dirty.
    eg.rebuild();

    let mut i = 0;
    loop {
        let mut body = || {
            stopper.check_limits(eg)?;
            detour_step(i, roots, rws, eg, &stopper, cf, cfg_offset, cfg_unreachable_cost, &mut sched)?;
            stopper.check_limits(eg)?;

            for h in hooks.iter_mut() {
                h(eg).map_err(StopReason::Other)?;
            }
            i += 1;

            Ok(())
        };

        if let Err(sr) = body() { stop_reason = sr; break }
    }

    let total_time = start.elapsed().as_secs_f64();

    let mut report = Runner::<L, ()>::new(()).run(&[]).report();

    report.stop_reason = stop_reason;
    report.total_time = total_time;

    report.iterations = i;
    report.egraph_nodes = eg.total_number_of_nodes();
    report.egraph_classes = eg.number_of_classes();
    report.memo_size = eg.total_size();

    // unknown
    report.rebuilds = 0;
    report.search_time = 0.0;
    report.apply_time = 0.0;
    report.rebuild_time = 0.0;

    report
}

fn detour_step<L: Language, N: Analysis<L> + Default>(i: usize, roots: &[Id], rws: &[Rewrite<L, N>], eg: &mut EGraph<L, N>, stopper: &Stopper, cf: fn(&L) -> Cost, cfg_offset: Cost, cfg_unreachable_cost: Cost, sched: &mut impl RewriteScheduler<L, N>) -> Result<(), StopReason> {
    if i%2 == 1 {
        let mut matches = Vec::new();

        for rw in rws {
            matches.push(sched.search_rewrite(i, eg, rw));
            stopper.check_limits(eg)?;
        }

        for (rw, ms) in rws.iter().zip(matches.into_iter()) {
            sched.apply_rewrite(i, eg, rw, ms);
            stopper.check_limits(eg)?;
        }

        eg.rebuild();

        return Ok(());
    }

    pat_detour_eqsat_step(i, roots, rws, eg, stopper, cf, cfg_offset, cfg_unreachable_cost, sched)
}

fn pat_detour_eqsat_step<L: Language, N: Analysis<L>>(i: usize, roots: &[Id], rws: &[Rewrite<L, N>], eg: &mut EGraph<L, N>, stopper: &Stopper, cf: fn(&L) -> Cost, cfg_offset: Cost, cfg_unreachable_cost: Cost, sched: &mut impl RewriteScheduler<L, N>) -> Result<(), StopReason> {
    let ex = Extractor::new(&eg, AdditiveCostFn(cf));
    let ctxt_cost = compute_ctxt_costs(roots, eg, &ex, cf);

    let mut matches: BTreeMap</*detour cost*/ Cost, Vec<(RewriteId, Id, Subst)>> = BTreeMap::default();

    for (rw_i, rw) in rws.iter().enumerate() {
        let lhs_pat = rw.searcher.get_pattern_ast().unwrap();

        for m in sched.search_rewrite(i, eg, rw) {
            stopper.check_limits(eg)?;

            let lhs = m.eclass;
            for subst in m.substs {
                let pat_cost = pat_cost(lhs_pat, &subst, &ex, cf);
                let cx_cost = *ctxt_cost.get(&lhs).unwrap_or(&cfg_unreachable_cost); // this is the cost you get from not being able to reach any root.
                let detour_cost = cx_cost + pat_cost;
                if !matches.contains_key(&detour_cost) {
                    matches.insert(detour_cost, Vec::new());
                }
                matches.get_mut(&detour_cost).unwrap().push((rw_i, lhs, subst));

                stopper.check_limits(eg)?;
            }
        }
    }

    let eg_data = |eg: &EGraph<_, _>| (eg.number_of_classes(), eg.total_size());

    let og_data = eg_data(eg);
    let mut found_cost = None;

    'outer: for (full_cost, new_apps) in matches {
        if let Some(found) = found_cost { if full_cost > found + cfg_offset { break } }
        for (rw_i, lhs, subst) in &new_apps {
            let rw = &rws[*rw_i];
            let pat_ast = rw.searcher.get_pattern_ast();
            rw.applier.apply_one(eg, *lhs, subst, pat_ast, rw.name);
            if eg_data(eg) != og_data && found_cost.is_none() { found_cost = Some(full_cost); }

            stopper.check_limits(eg)?;
        }
    }

    eg.rebuild();
    Ok(())
}

// === ctxt cost ===

fn compute_ctxt_costs<L: Language, N: Analysis<L>>(roots: &[Id], eg: &EGraph<L, N>, ex: &Extractor<AdditiveCostFn<L>, L, N>, cf: fn(&L) -> Cost) -> HashMap<Id, Cost> {
    let mut ctxt_cost = HashMap::new();

    let mut queue: MinPrioQueue<Cost, Id> = MinPrioQueue::new();

    // initial
    for root in roots {
        queue.push(0, *root);
    }

    while let Some((cst, i)) = queue.pop() {
        if ctxt_cost.contains_key(&i) { continue }
        ctxt_cost.insert(i, cst);
        for e in &eg[i].nodes {
            let e_cost = AdditiveCostFn(cf).cost(e, |k| ex.find_best_cost(k));
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

fn pat_cost<L: Language, N: Analysis<L>>(pat: &PatternAst<L>, subst: &Subst, ex: &Extractor<AdditiveCostFn<L>, L, N>, cf: fn(&L) -> Cost) -> Cost {
    let mut vec: Vec<Cost> = Vec::new();
    for i in 0..pat.as_ref().len() {
        let cost = match &pat[i.into()] {
            ENodeOrVar::ENode(n) => AdditiveCostFn(cf).cost(n, |x| vec[usize::from(x)]),
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

// === AdditiveCostFn ===

struct AdditiveCostFn<L: Language>(fn(&L) -> Cost);

impl<L: Language> CostFunction<L> for AdditiveCostFn<L> {
    type Cost = Cost;

    fn cost<C>(&mut self, enode: &L, costs: C) -> Self::Cost where C: FnMut(Id) -> Self::Cost {
        enode.children().iter().copied().map(costs).fold(self.0(enode), |x, y| x+y)
    }
}

// === Stopper ===

struct Stopper {
    start: Instant,
    time_limit: Duration,
    node_limit: usize,
}

impl Stopper {
    fn check_limits<L: Language, N: Analysis<L>>(&self, eg: &EGraph<L, N>) -> Result<(), StopReason> {
        let elapsed = self.start.elapsed();
        if elapsed > self.time_limit { return Err(StopReason::TimeLimit(elapsed.as_secs_f64())) }

        let size = eg.total_size();
        if size > self.node_limit { return Err(StopReason::NodeLimit(size)) }

        Ok(())
    }
}
