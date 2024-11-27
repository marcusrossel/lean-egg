import Egg.Core.Gen.Builtins
import Egg.Core.Gen.TcProjs
import Egg.Core.Gen.TcSpecs
import Egg.Core.Gen.Explosion
import Egg.Tactic.Premises.Parse
import Egg.Tactic.Trace
import Egg.Tactic.Tags
import Lean

open Lean hiding HashSet
open Meta Elab Tactic
open Std (HashSet)

namespace Egg.Premises

-- TODO: Perform pruning during generation, not after.

private def tracePremises
    (basic : WithSyntax Rewrites) (tagged builtins tc ex pruned : Rewrites)
    (facts : WithSyntax Facts) (cfg : Config.DefEq) : TacticM Unit := do
  let cls := `egg.rewrites
  withTraceNode cls (fun _ => return "Rewrites") do
    withTraceNode cls (fun _ => return m!"Basic ({basic.elems.size})") do basic.elems.trace basic.stxs cls
    withTraceNode cls (fun _ => return m!"Tagged ({tagged.size})") do tagged.trace #[] cls
    withTraceNode cls (fun _ => return m!"Generated ({tc.size})") do tc.trace #[] cls
    withTraceNode cls (fun _ => return m!"Exploded ({ex.size})") do ex.trace #[] cls
    withTraceNode cls (fun _ => return m!"Builtin ({builtins.size})") do builtins.trace #[] cls
    withTraceNode cls (fun _ => return m!"Hypotheses ({facts.elems.size})") do
      facts.elems.trace facts.stxs cls
    withTraceNode cls (fun _ => return "Definitional") do
      if cfg.beta    then Lean.trace cls fun _ => "β-Reduction"
      if cfg.eta     then Lean.trace cls fun _ => "η-Reduction"
      if cfg.natLit then Lean.trace cls fun _ => "Natural Number Literals"
    withTraceNode cls (fun _ => return m!"Pruned ({pruned.size})") do pruned.trace #[] cls

partial def gen
    (goal : Congr) (ps : TSyntax `egg_premises) (guides : Guides) (cfg : Config)
    (amb : MVars.Ambient) : TacticM (Rewrites × Facts) := do
  let tagged ← genTagged cfg amb
  let ⟨⟨basic, basicStxs⟩, facts⟩ ← Premises.elab { cfg with amb } ps
  let (basic, basicStxs, pruned₁) ← prune basic basicStxs (remove := tagged)
  let builtins ← if cfg.builtins then Rewrites.builtins { cfg with amb } else pure #[]
  let (builtins, _, pruned₂) ← prune builtins (remove := tagged ++ basic)
  let tc ← genTcRws (tagged ++ basic ++ builtins) facts.elems -- Note: We check the config in `genTcRws`.
  let (tc, _, pruned₃) ← prune tc (remove := tagged ++ basic ++ builtins)
  let ex ← if cfg.explosion then genExplosions basic else pure #[]
  let (ex, _, pruned₄) ← prune ex (remove := tagged ++ basic ++ builtins ++ tc)
  tracePremises ⟨basic, basicStxs⟩ tagged builtins tc ex (pruned₁ ++ pruned₂ ++ pruned₃ ++ pruned₄) facts cfg
  let rws := tagged ++ basic ++ builtins ++ tc ++ ex
  catchInvalidConditionals rws
  return (rws, facts.elems)
where
  genTagged (cfg : Config) (amb : MVars.Ambient) : TacticM Rewrites := do
    let some _ := cfg.basket? | return #[]
    -- TODO: This should use the basket name to find the proper extension.
    let prems := extension.getState (← getEnv)
    Premises.elabTagged prems { cfg with amb }

  genTcRws (rws : Rewrites) (facts : Facts) : TacticM Rewrites := do
    let mut projTodo := #[]
    let mut specTodo := #[]
    let mut tcRws := #[]
    let mut covered : HashSet TcProj := ∅
    if cfg.genTcProjRws then projTodo := goal.tcProjTargets .goal ++ facts.tcProjTargets ++ guides.tcProjTargets ++ rws.tcProjTargets
    if cfg.genTcSpecRws then specTodo := rws
    while (cfg.genTcProjRws && !projTodo.isEmpty) || (cfg.genTcSpecRws && !specTodo.isEmpty) do
      if cfg.genTcProjRws then
        let (projRws, cov) ← genTcProjReductions projTodo covered { cfg with amb }
        projTodo := #[]
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

  prune (rws : Rewrites) (stx? : Option (Array Syntax) := none) (remove : Rewrites) :
      MetaM (Rewrites × Array Syntax × Rewrites) := open SynthInstance in do
    let mut keep := #[]
    let mut keepStx := #[]
    let mut pruned := #[]
    let contains (tgts : Rewrites) (rw : Rewrite) : MetaM Bool := do
      let lhsAbs ← abstractMVars rw.lhs
      let rhsAbs ← abstractMVars rw.rhs
      let conds  ← rw.conds.mapM (AbstractMVarsResult.expr <$> abstractMVars ·.expr)
      tgts.anyM fun t => do
        unless lhsAbs.expr == (← abstractMVars t.lhs).expr do return false
        unless rhsAbs.expr == (← abstractMVars t.rhs).expr do return false
        let tConds ← t.conds.mapM (AbstractMVarsResult.expr <$> abstractMVars ·.expr)
        return conds == tConds
    for rw in rws, idx in [:rws.size] do
      if ← contains keep   rw then pruned := pruned.push rw; continue
      if ← contains remove rw then pruned := pruned.push rw; continue
      keep := keep.push rw
      if let some stx := stx? then keepStx := keepStx.push stx[idx]!
    return (keep, keepStx, pruned)

  catchInvalidConditionals (rws : Rewrites) : MetaM Unit := do
    for rw in rws do
      for cond in rw.conds do
        for m in cond.mvars.expr do
          unless rw.mvars.lhs.expr.contains m || rw.mvars.rhs.expr.contains m do
            throwError "egg does not currently support rewrites with unbound conditions (expression)"
        for m in cond.mvars.lvl do
          unless rw.mvars.lhs.lvl.contains m || rw.mvars.rhs.lvl.contains m do
            throwError "egg does not currently support rewrites with unbound conditions (level)"
