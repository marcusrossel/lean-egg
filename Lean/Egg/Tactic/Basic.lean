import Egg.Core.Request.Basic
import Egg.Core.Explanation.Proof
import Egg.Core.Gen.TcProjs
import Egg.Core.Gen.TcSpecs
import Egg.Tactic.Config.Option
import Egg.Tactic.Config.Modifier
import Egg.Tactic.Base
import Egg.Tactic.Guides
import Egg.Tactic.Premises
import Egg.Tactic.Trace
import Std.Tactic.Exact
import Lean

open Lean Meta Elab Tactic

namespace Egg

-- Note: If `base? ≠ none`, the goal is an auxiliary goal and needs to be handled specially after
--       proof reconstruction.
private structure Goal where
  id    : MVarId
  type  : Congr
  base? : Option FVarId

private def Goal.tcProjTargets (goal : Goal) : Array TcProjTarget := #[
  { expr := goal.type.lhs, src := .goal, loc := .left },
  { expr := goal.type.rhs, src := .goal, loc := .right }
]

private def parseGoal (goal : MVarId) (base? : Option (TSyntax `egg_base)) : MetaM Goal := do
  let goalType ← normalize (← goal.getType') .noReduce
  let base? ← base?.mapM parseBase
  let cgr ← getCongr goalType base?
  return { id := goal, type := cgr, base? }
where
  getCongr (goalType : Expr) (base? : Option FVarId) : MetaM Congr := do
    if let some base := base? then
      return { lhs := ← base.getType, rhs := goalType, rel := .eq : Congr }
    else if let some c ← Congr.from? goalType then
      return c
    else
      throwError "expected goal to be of type '=' or '↔', but found:\n{← ppExpr goalType}"

-- TODO: We should also consider the level mvars of all `Fact`s.
private def collectAmbientMVars (goal : Goal) (guides : Guides) : MetaM MVars.Ambient := do
  let expr ← MVars.Ambient.Expr.get
  let goalLvl := (← MVars.collect (← goal.type.expr)).lvl
  let guidesLvl ← guides.foldlM (init := ∅) fun res g => return res.merge (← MVars.collect g.expr).lvl
  return { expr, lvl := goalLvl.merge guidesLvl }

private def tracePremises (ps : Premises) (tc : Rewrites) (cfg : Config.Gen) : TacticM Unit := do
  let cls := `egg.rewrites
  withTraceNode cls (fun _ => return "Rewrites") do
    withTraceNode cls (fun _ => return m!"Basic ({ps.rws.size})") do ps.rws.trace ps.rwsStx cls
    withTraceNode cls (fun _ => return m!"Generated ({tc.size})") do tc.trace #[] cls
    withTraceNode cls (fun _ => return "Definitional") do
      if cfg.genBetaRw    then Lean.trace cls fun _ => "β-Reduction"
      if cfg.genEtaRw     then Lean.trace cls fun _ => "η-Reduction"
      if cfg.genNatLitRws then Lean.trace cls fun _ => "Natural Number Literals"
    withTraceNode cls (fun _ => return m!"Hypotheses ({ps.facts.size})") do
      ps.facts.trace ps.factsStx cls

private partial def genPremises
    (goal : Goal) (ps : TSyntax `egg_prems) (guides : Guides) (cfg : Config) (amb : MVars.Ambient) :
    TacticM (Rewrites × Facts) := do
  let ps ← Premises.parse cfg amb ps
  let tcRws ← genTcRws ps
  tracePremises ps tcRws cfg
  catchInvalidConditionals ps.rws ps.rwsStx
  return (ps.rws ++ tcRws, ps.facts)
where
  genTcRws (ps : Premises) : TacticM Rewrites := do
    let mut projTodo := #[]
    let mut specTodo := #[]
    let mut tcRws := #[]
    let mut covered : HashSet TcProj := ∅
    if cfg.genTcProjRws then projTodo := goal.tcProjTargets ++ ps.facts.tcProjTargets ++ guides.tcProjTargets ++ ps.rws.tcProjTargets
    if cfg.genTcSpecRws then specTodo := ps.rws
    while (cfg.genTcProjRws && !projTodo.isEmpty) || (cfg.genTcSpecRws && !specTodo.isEmpty) do
      if cfg.genTcProjRws then
        let (projRws, cov) ← genTcProjReductions projTodo covered cfg amb
        covered  := cov
        specTodo := specTodo ++ projRws
        tcRws    := tcRws ++ projRws
      if cfg.genTcSpecRws then
        let specRws ← genTcSpecializations specTodo cfg
        specTodo := #[]
        projTodo := specRws.tcProjTargets
        tcRws    := tcRws ++ specRws
    return tcRws

  catchInvalidConditionals (rws : Rewrites) (stx : Array Syntax) : MetaM Unit := do
    for rw in rws, s in stx do
      for cond in rw.conds do
        for m in cond.mvars.expr do
          unless rw.mvars.lhs.expr.contains m || rw.mvars.rhs.expr.contains m do
            throwErrorAt s "egg does not currently support rewrites with unbound conditions (expression)"
        for m in cond.mvars.lvl do
          unless rw.mvars.lhs.lvl.contains m || rw.mvars.rhs.lvl.contains m do
            throwErrorAt s "egg does not currently support rewrites with unbound conditions (level)"

private def processRawExpl
    (rawExpl : Explanation.Raw) (goal : Goal) (rws : Rewrites) (facts : Facts)
    (amb : MVars.Ambient) (cfg : Config) (egraph? : Option EGraph) : TacticM Expr := do
  let expl ← rawExpl.parse
  let some egraph := egraph? | throwError "egg: internal error: e-graph is absent"
  let proof ← expl.proof rws facts egraph cfg amb
  proof.trace `egg.proof
  let mut prf ← proof.prove goal.type
  prf ← instantiateMVars prf
  withTraceNode `egg.proof.term (fun _ => return "Proof Term") do trace[egg.proof.term] prf
  -- When `goal.base? = some base`, then `proof` is a proof of `base = <goal type>`. We turn this
  -- into a proof of `<goal type>` here.
  if let some base := goal.base? then prf ← mkEqMP prf (.fvar base)
  catchLooseMVars prf amb
  return prf
where
  catchLooseMVars (prf : Expr) (amb : MVars.Ambient) : MetaM Unit := do
    let mvars ← MVars.collect prf
    for mvar in mvars.expr do
      unless amb.expr.contains mvar do
        throwError m!"egg: final proof contains expression mvar {Expr.mvar mvar}"
    for lmvar in mvars.lvl do
      unless amb.lvl.contains lmvar do
        throwError m!"egg: final proof contains level mvar {Level.mvar lmvar}"

open Config.Modifier (egg_cfg_mod)

elab "egg " mod:egg_cfg_mod rws:egg_prems base:(egg_base)? guides:(egg_guides)? : tactic => do
  let goal ← getMainGoal
  let mod  ← Config.Modifier.parse mod
  let cfg := (← Config.fromOptions).modify mod
  cfg.trace `egg.config
  goal.withContext do
    let goal ← parseGoal goal base
    let guides := (← guides.mapM Guides.parseGuides).getD #[]
    let amb ← collectAmbientMVars goal guides
    amb.trace `egg.ambient
    -- We increase the mvar context depth, so that ambient mvars aren't unified during proof
    -- reconstruction. Note that this also means that we can't assign the `goal` mvar within this
    -- do-block.
    let proof? ← withNewMCtxDepth do
      let (rws, facts) ← genPremises goal rws guides cfg amb
      let req ← Request.encoding goal.type rws facts guides cfg amb
      withTraceNode `egg.encoded (fun _ => return "Encoded") do req.trace `egg.encoded
      if let .beforeEqSat := cfg.exitPoint then return none
      let (rawExpl, egraph?) := req.run
      if rawExpl.isEmpty then throwError "egg failed to prove goal"
      withTraceNode `egg.explanation (fun _ => return "Explanation") do trace[egg.explanation] rawExpl
      if let .beforeProof := cfg.exitPoint then return none
      return some (← processRawExpl rawExpl goal rws facts amb cfg egraph?)
    if let some proof := proof?
    then goal.id.assignIfDefeq proof
    else goal.id.admit

-- WORKAROUND: This fixes `Tests/EndOfInput *`.
macro "egg" mod:egg_cfg_mod : tactic => `(tactic| egg $mod)
