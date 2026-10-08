use std::cell::RefCell;
use std::collections::HashMap;
use std::ffi::c_void;
use rs2::*;
use crate::basic::*;
use crate::result::*;
use crate::lean_expr::*;
use crate::analysis::*;
use crate::bvar_correction::*;
use crate::egraph::*;
use crate::proof::*;
use crate::string_to_c_str;
use crate::valid_match::*;
use crate::is_synthable;
use crate::util::*;

// Analogous to egg's `Applier` trait. The `from` e-class is the instantiation of the rewrite's
// searcher pattern.
pub trait Applier {
    fn apply_one(&self, graph: &mut LeanEGraph, from: PId, subst: &LeanSubst, rule: &str);
}

// Plain patterns are appliers which union their instantiation with the matched e-class.
impl Applier for LeanPattern {

    fn apply_one(&self, graph: &mut LeanEGraph, from: PId, subst: &LeanSubst, rule: &str) {
        union_instantiation(graph, from, self, subst, rule);
    }
}

// Analogous to `Rewrite::new` in egg.
pub fn mk_rewrite(name: impl ToString, searcher: LeanPattern, applier: impl Applier + 'static) -> LeanRewrite {
    let name = name.to_string();
    (searcher, Box::new(move |from: PId, subst: LeanSubst, graph: &mut LeanEGraph| {
        applier.apply_one(graph, from, &subst, &name)
    }))
}

// Analogous to egg's `rewrite!` macro.
macro_rules! rewrite {
    ($name:expr; $lhs:tt => $rhs:tt) => {
        $crate::rewrite::mk_rewrite($name, $crate::util::pat($lhs), $crate::rewrite::applier!($rhs))
    };
    ($name:expr; $lhs:tt <=> $rhs:tt) => {
        vec![
            $crate::rewrite::rewrite!($name; $lhs => $rhs),
            $crate::rewrite::rewrite!(format!("{}-rev", $name); $rhs => $lhs),
        ]
    };
}

macro_rules! applier {
    ($rhs:literal)          => { $crate::util::pat($rhs) };
    ({ $($rhs:tt)* })       => { $($rhs)* };
}

pub(crate) use rewrite;
pub(crate) use applier;

pub struct RewriteConfig {
    binders_are_active: bool,
    subgoals: bool,
    env: *const c_void
}

impl Config {

    pub fn to_rw_config(&self, binders_are_active: bool, env: *const c_void) -> RewriteConfig {
        RewriteConfig {
            binders_are_active,
            subgoals: self.subgoals,
            env
        }
    }
}

pub struct RewriteTemplate {
    pub name:       String,
    pub lhs:        LeanPattern,
    pub rhs:        LeanPattern,
    pub prop_conds: Vec<LeanPattern>,
    pub tc_conds:   Vec<LeanPattern>,
    pub weak_vars:  Vec<PVar>,
    pub blocks:     Vec<LeanTerm>
}

pub struct GroundEq {
    pub name: String,
    pub lhs : LeanTerm,
    pub rhs : LeanTerm
}

impl RewriteTemplate {

    pub fn to_rewrite(self, cfg: RewriteConfig) -> Res<Either<LeanRewrite, GroundEq>> {
        // If the rewrite contains neither conditions nor pattern variables, it's a ground equation.
        if self.prop_conds.is_empty() && self.tc_conds.is_empty() &&
           pattern_vars(&self.lhs).is_empty() && pattern_vars(&self.rhs).is_empty() {
            return Ok(Either::R(GroundEq { name: self.name, lhs: self.lhs, rhs: self.rhs }))
        }

        let lhs = if self.prop_conds.is_empty() || cfg.subgoals {
            self.lhs.clone()
        } else {
            let mut str = format!("(= {:?} {:?})", self.lhs, self.lhs);

            for cond in self.prop_conds.iter() {
                str = format!("(app (app (const \"And\") {}) {:?})", str, cond);
            }

            str = format!("(fact {})", str);
            parse_pattern(&str).expect("Failed to parse lhs in 'RewriteTemplate.to_rewrite'.")
        };

        let applier = LeanApplier {
            lhs: self.lhs, rhs: self.rhs, tc_conds: self.tc_conds, prop_conds: self.prop_conds,
            weak_vars: self.weak_vars, blocks: self.blocks, cfg
        };
        Ok(Either::L(mk_rewrite(self.name, lhs, applier)))
    }
}

struct LeanApplier {
    pub lhs:        LeanPattern,
    pub rhs:        LeanPattern,
    pub tc_conds:   Vec<LeanPattern>,
    pub prop_conds: Vec<LeanPattern>,
    pub weak_vars:  Vec<PVar>,
    pub blocks:     Vec<LeanTerm>, // TODO: This could be extended to cover patterns, if needed.
    pub cfg:        RewriteConfig,
}

impl Applier for LeanApplier {

    fn apply_one(&self, graph: &mut LeanEGraph, _: PId, subst: &LeanSubst, rule: &str) {
        if is_primitive_pattern_subst(&self.lhs, graph, subst) { return }

        let mut var_depths: Option<HashMap<PVar, u64>> = None;
        if self.cfg.binders_are_active {
            match match_is_valid(subst, &self.lhs, graph) {
                MatchValidity::Invalid   => return,
                MatchValidity::Valid(vd) => var_depths = Some(vd)
            }
        }

        for tc_cond in &self.tc_conds {
            if !cond_is_synthable(tc_cond, subst, self.cfg.env) {
                return
            }
        }

        let mut rule = rule.to_string();
        if self.cfg.subgoals {
            if !self.blocks.is_empty() {
                // If subgoals are activated, still check that no conditional proposition is blocked.
                for prop_cond in self.prop_conds.iter() {
                    let prop_cond_expr = with_recorded_enodes(|enodes| instantiate_term(prop_cond, enodes, subst));
                    if self.blocks.contains(&prop_cond_expr) {
                        return
                    }
                }
            }
        } else if !self.weak_vars.is_empty() {
            // If subgoals are not activated, assign weak vars (if any exists).
            for var in &self.weak_vars {
                let assignment = format!("{}={}", var.to_string().replace("?", ","), subst[var].1.0);
                rule.push_str(&assignment);
            }
        }

        // The searcher of this rewrite may differ from `self.lhs` (cf. `to_rewrite`), so we
        // instantiate `self.lhs` instead of using the matched e-class.
        let from = instantiate(&self.lhs, graph, subst);

        // A substitution needs no shifting if it does not map any variables to e-classes containing
        // loose bvars. This is the case exactly when `var_depths` is empty.
        if self.cfg.binders_are_active && !var_depths.clone().unwrap().is_empty() {
            let shifted_rhs = correct_bvar_indices(&self.rhs, var_depths.unwrap());
            union_instantiation(graph, from, &shifted_rhs, subst, &rule);
        } else {
            union_instantiation(graph, from, &self.rhs, subst, &rule);
        }
    }
}

thread_local! {
    static TC_CACHE: RefCell<HashMap<LeanTerm, bool>> = RefCell::new(Default::default());
}

fn cond_is_synthable(cond: &LeanPattern, subst: &LeanSubst, env: *const c_void) -> bool {
    let ast = with_recorded_enodes(|enodes| instantiate_term(cond, enodes, subst));
    TC_CACHE.with_borrow_mut(|cache|
        if let Some(result) = cache.get(&ast) {
            *result
        } else {
            let str = string_to_c_str(format!("{:?}", ast));
            let result = unsafe { is_synthable(env, str) };
            cache.insert(ast, result);
            result
        }
    )
}

fn is_primitive_pattern_subst(pat: &LeanPattern, graph: &LeanEGraph, subst: &LeanSubst) -> bool {
    match pat {
        Pattern::PVar(x)    => is_primitive(subst[x].1, graph),
        Pattern::Node(n, _) => is_primitive_node(n),
        Pattern::G(..)      => unreachable!("patterns are not proof-annotated")
    }
}

pub fn is_primitive_node(node: &LeanExpr) -> bool {
    matches!(node,
            LeanExpr::Nat(_) | LeanExpr::Str(_) | LeanExpr::Fun(_) | LeanExpr::UVar(_) | LeanExpr::Param(_) |
            LeanExpr::Succ(_) | LeanExpr::Max(_) | LeanExpr::IMax(_) | LeanExpr::Fact(_) | LeanExpr::Unknown
    )
}

// Mirrors egg, where `graph[x].nodes.first()` is the least e-node of an e-class.
pub fn is_primitive(x: Id, graph: &LeanEGraph) -> bool {
    class_nodes(x, graph).iter().min().is_some_and(is_primitive_node)
}
