import Egg.Core.Gen.Builtins
import Egg.Core.Gen.TcProjs
import Egg.Core.Gen.TcSpecs
import Egg.Tactic.Premises.Parse
import Egg.Tactic.Trace
import Lean

open Lean Meta Elab Tactic

namespace Egg.Premises

private def tracePremises (ps : Premises) (builtins tc : Rewrites) (cfg : Config.Gen) : TacticM Unit := do
  let cls := `egg.rewrites
  withTraceNode cls (fun _ => return "Rewrites") do
    withTraceNode cls (fun _ => return m!"Basic ({ps.rws.elems.size})") do ps.rws.elems.trace ps.rws.stxs cls
    withTraceNode cls (fun _ => return m!"Generated ({tc.size})") do tc.trace #[] cls
    withTraceNode cls (fun _ => return m!"Builtin ({builtins.size})") do builtins.trace #[] cls
    withTraceNode cls (fun _ => return m!"Hypotheses ({ps.facts.elems.size})") do
      ps.facts.elems.trace ps.facts.stxs cls
    withTraceNode cls (fun _ => return "Definitional") do
      if cfg.genBetaRw    then Lean.trace cls fun _ => "β-Reduction"
      if cfg.genEtaRw     then Lean.trace cls fun _ => "η-Reduction"
      if cfg.genNatLitRws then Lean.trace cls fun _ => "Natural Number Literals"

partial def gen
    (goal : Congr) (ps : TSyntax `egg_premises) (guides : Guides) (cfg : Config)
    (amb : MVars.Ambient) : TacticM (Rewrites × Facts) := do
  let ps ← Premises.elab { norm? := cfg, amb } ps
  let builtins ← if cfg.builtins then Rewrites.builtins { norm? := cfg, amb } else pure #[]
  let tcRws ← genTcRws (ps.rws.elems ++ builtins) ps.facts.elems
  tracePremises ps builtins tcRws cfg
  catchInvalidConditionals ps.rws
  return (ps.rws.elems ++ builtins ++ tcRws, ps.facts.elems)
where
  genTcRws (rws : Rewrites) (facts : Facts) : TacticM Rewrites := do
    let mut projTodo := #[]
    let mut specTodo := #[]
    let mut tcRws := #[]
    let mut covered : HashSet TcProj := ∅
    if cfg.genTcProjRws then projTodo := goal.tcProjTargets .goal ++ facts.tcProjTargets ++ guides.tcProjTargets ++ rws.tcProjTargets
    if cfg.genTcSpecRws then specTodo := rws
    while (cfg.genTcProjRws && !projTodo.isEmpty) || (cfg.genTcSpecRws && !specTodo.isEmpty) do
      if cfg.genTcProjRws then
        let (projRws, cov) ← genTcProjReductions projTodo covered cfg amb
        covered  := cov
        specTodo := specTodo ++ projRws
        tcRws    := tcRws ++ projRws
      if cfg.genTcSpecRws then
        let goalType? ← do if cfg.genGoalTcSpec then pure <| some (← goal.type) else pure none
        let specRws ← genTcSpecializations specTodo cfg goalType?
        specTodo := #[]
        projTodo := specRws.tcProjTargets
        tcRws    := tcRws ++ specRws
    return tcRws

  catchInvalidConditionals (rws : WithSyntax Rewrites) : MetaM Unit := do
    for rw in rws.elems, stx in rws.stxs do
      for cond in rw.conds do
        for m in cond.mvars.expr do
          unless rw.mvars.lhs.expr.contains m || rw.mvars.rhs.expr.contains m do
            throwErrorAt stx "egg does not currently support rewrites with unbound conditions (expression)"
        for m in cond.mvars.lvl do
          unless rw.mvars.lhs.lvl.contains m || rw.mvars.rhs.lvl.contains m do
            throwErrorAt stx "egg does not currently support rewrites with unbound conditions (level)"
