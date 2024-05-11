import Egg.Core.Gen.Builtins
import Egg.Core.Gen.TcProjs
import Egg.Core.Gen.TcSpecs
import Egg.Tactic.Premises.Parse
import Egg.Tactic.Trace
import Lean

open Lean Meta Elab Tactic

namespace Egg.Premises

-- TODO: Perform pruning during generation, not after.

private def tracePremises
    (basic : WithSyntax Rewrites) (builtins tc pruned : Rewrites) (facts : WithSyntax Facts)
    (cfg : Config.Gen) : TacticM Unit := do
  let cls := `egg.rewrites
  withTraceNode cls (fun _ => return "Rewrites") do
    withTraceNode cls (fun _ => return m!"Basic ({basic.elems.size})") do basic.elems.trace basic.stxs cls
    withTraceNode cls (fun _ => return m!"Generated ({tc.size})") do tc.trace #[] cls
    withTraceNode cls (fun _ => return m!"Builtin ({builtins.size})") do builtins.trace #[] cls
    withTraceNode cls (fun _ => return m!"Hypotheses ({facts.elems.size})") do
      facts.elems.trace facts.stxs cls
    withTraceNode cls (fun _ => return "Definitional") do
      if cfg.genBetaRw    then Lean.trace cls fun _ => "β-Reduction"
      if cfg.genEtaRw     then Lean.trace cls fun _ => "η-Reduction"
      if cfg.genNatLitRws then Lean.trace cls fun _ => "Natural Number Literals"
    withTraceNode cls (fun _ => return m!"Pruned ({pruned.size})") do pruned.trace #[] cls

partial def gen
    (goal : Congr) (ps : TSyntax `egg_premises) (guides : Guides) (cfg : Config)
    (amb : MVars.Ambient) : TacticM (Rewrites × Facts) := do
  let ⟨⟨basic, basicStxs⟩, facts⟩ ← Premises.elab { norm? := cfg, amb } ps
  let (basic, basicStxs, pruned₁) ← prune basic basicStxs (remove := #[])
  let builtins ← if cfg.builtins then Rewrites.builtins { norm? := cfg, amb } else pure #[]
  let (builtins, _, pruned₂) ← prune builtins (remove := basic)
  let tc ← genTcRws (basic ++ builtins) facts.elems
  let (tc, _, pruned₃) ← prune tc (remove := basic ++ builtins)
  tracePremises ⟨basic, basicStxs⟩ builtins tc (pruned₁ ++ pruned₂ ++ pruned₃) facts cfg
  let rws := basic ++ builtins ++ tc
  catchInvalidConditionals rws
  return (rws, facts.elems)
where
  -- See: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Expr.20equal.20up.20to.20mvars
  prune (rws : Rewrites) (stx? : Option (Array Syntax) := none) (remove : Rewrites) :
      MetaM (Rewrites × Array Syntax × Rewrites) := open SynthInstance in do
    let mut keep := #[]
    let mut keepStx := #[]
    let mut pruned := #[]
    let contains (tgts : Rewrites) (lhsKey rhsKey : Expr) : MetaM Bool :=
      tgts.anyM fun t =>
        (return lhsKey == (← mkTableKey t.lhs)) <&&>
        (return rhsKey == (← mkTableKey t.rhs))
    for rw in rws, idx in [:rws.size] do
      let rwLhs ← mkTableKey rw.lhs
      let rwRhs ← mkTableKey rw.rhs
      if ← contains keep   rwLhs rwRhs then pruned := pruned.push rw; continue
      if ← contains remove rwLhs rwRhs then pruned := pruned.push rw; continue
      keep := keep.push rw
      if let some stx := stx? then keepStx := keepStx.push stx[idx]!
    return (keep, keepStx, pruned)

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

  catchInvalidConditionals (rws : Rewrites) : MetaM Unit := do
    for rw in rws do
      for cond in rw.conds do
        for m in cond.mvars.expr do
          unless rw.mvars.lhs.expr.contains m || rw.mvars.rhs.expr.contains m do
            throwError "egg does not currently support rewrites with unbound conditions (expression)"
        for m in cond.mvars.lvl do
          unless rw.mvars.lhs.lvl.contains m || rw.mvars.rhs.lvl.contains m do
            throwError "egg does not currently support rewrites with unbound conditions (level)"
