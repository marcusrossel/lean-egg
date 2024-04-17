import Egg.Core.Request
import Egg.Core.Explanation.Proof
import Egg.Core.Gen.TcProjs
import Egg.Core.Gen.TcSpecs
import Egg.Tactic.Config.Option
import Egg.Tactic.Config.Modifier
import Egg.Tactic.Explanation
import Egg.Tactic.Base
import Egg.Tactic.Guides
import Egg.Tactic.Rewrites
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
  { expr := goal.type.lhs, src := .goal, side? := some .left },
  { expr := goal.type.rhs, src := .goal, side? := some .right }
]

private abbrev AmbientMVars := PersistentHashMap MVarId MetavarDecl

private def AmbientMVars.get : MetaM AmbientMVars :=
  return (← getMCtx).decls

private def parseGoal (goal : MVarId) (base? : Option (TSyntax `egg_base)) : MetaM Goal := do
  let goalType ← normalize (← goal.getType') (beta := false) (eta := false)
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

private def traceRewrites
    (basic : Rewrites) (stx : Array Syntax) (tc : Rewrites) (cfg : Config.Gen) : TacticM Unit := do
  let cls := `egg.rewrites
  withTraceNode cls (fun _ => return "Rewrites") do
    withTraceNode cls (fun _ => return m!"Basic ({basic.size})") do basic.trace stx cls
    withTraceNode cls (fun _ => return m!"Generated ({tc.size})") do tc.trace #[] cls
    withTraceNode cls (fun _ => return "Definitional") do
      if cfg.genBetaRw    then Lean.trace cls fun _ => "β-Reduction"
      if cfg.genEtaRw     then Lean.trace cls fun _ => "η-Reduction"
      if cfg.genNatLitRws then Lean.trace cls fun _ => "Natural Number Literals"

private partial def genRewrites
    (goal : Goal) (rws : TSyntax `egg_rws) (guides : Guides) (cfg : Config) : TacticM Rewrites := do
  let (rws, stx) ← Rewrites.parse cfg.betaReduceRws cfg.etaReduceRws rws
  let tcRws ← genTcRws rws
  traceRewrites rws stx tcRws cfg.toGen
  return rws ++ tcRws
where
  genTcRws (rws : Rewrites) : TacticM Rewrites := do
    let mut projTodo := #[]
    let mut specTodo := #[]
    let mut tcRws := #[]
    let mut covered : HashSet TcProj := ∅
    if cfg.genTcProjRws then projTodo := goal.tcProjTargets ++ guides.tcProjTargets ++ rws.tcProjTargets
    if cfg.genTcSpecRws then specTodo := rws
    while (cfg.genTcProjRws && !projTodo.isEmpty) || (cfg.genTcSpecRws && !specTodo.isEmpty) do
      if cfg.genTcProjRws then
        let (projRws, cov) ← genTcProjReductions projTodo covered cfg.betaReduceRws cfg.etaReduceRws
        covered  := cov
        specTodo := specTodo ++ projRws
        tcRws    := tcRws ++ projRws
      if cfg.genTcSpecRws then
        let specRws ← genTcSpecializations specTodo
        specTodo := #[]
        projTodo := specRws.tcProjTargets
        tcRws    := tcRws ++ specRws
    return tcRws

private def processRawExpl
    (rawExpl : Explanation.Raw) (goal : Goal) (rws : Rewrites) (cfg : Config.Debug)
    (amb : AmbientMVars) : TacticM Unit := do
  if rawExpl.isEmpty then throwError "egg failed to prove goal"
  withTraceNode `egg.explanation (fun _ => return "Explanation") do trace[egg.explanation] rawExpl
  if cfg.exitPoint == .beforeProof then goal.id.admit; return
  let expl ← rawExpl.parse
  let proof ← expl.proof rws
  let mut prf ← proof.prove goal.type
  prf ← instantiateMVars prf
  catchLooseMVars prf amb
  -- When `goal.base? = some base`, then `proof` is a proof of `base = <goal type>`. We turn this
  -- into a proof of `<goal type>` here.
  if let some base := goal.base? then prf ← mkEqMP prf (.fvar base)
  goal.id.assignIfDefeq prf
where
  catchLooseMVars (prf : Expr) (amb : AmbientMVars) : MetaM Unit := do
    for mvar in (prf.collectMVars {}).result do
      unless amb.contains mvar do throwError s!"egg: final proof contains mvar {mvar.name}"

private def traceRequest (req : Request) : TacticM Unit := do
  let cls := `egg.encoded
  withTraceNode cls (fun _ => return "Encoded") do
    req.trace cls

open Config.Modifier (egg_cfg_mod)

elab "egg " mod:egg_cfg_mod rws:egg_rws base:(egg_base)? guides:(egg_guides)? : tactic => do
  let goal ← getMainGoal
  let mod  ← Config.Modifier.parse mod
  let cfg := (← Config.fromOptions).modify mod
  cfg.trace `egg.config
  goal.withContext do
    let amb     ← AmbientMVars.get
    let goal    ← parseGoal goal base
    let guides := (← guides.mapM Guides.parseGuides).getD #[]
    let rws     ← genRewrites goal rws guides cfg
    let req     ← Request.encoding goal.type rws guides cfg
    traceRequest req
    if cfg.exitPoint == .beforeEqSat then goal.id.admit; return
    let rawExpl := req.run
    processRawExpl rawExpl goal rws cfg.toDebug amb

-- WORKAROUND: This fixes `Tests/EndOfInput *`.
macro "egg" mod:egg_cfg_mod : tactic => `(tactic| egg $mod)
