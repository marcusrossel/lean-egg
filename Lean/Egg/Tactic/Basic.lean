import Egg.Core.Request
import Egg.Core.Explanation.Proof
import Egg.Core.Gen.TcProjs
import Egg.Core.Gen.TcSpecs
import Egg.Tactic.Config.Option
import Egg.Tactic.Config.Modifier
import Egg.Tactic.Explanation
import Egg.Tactic.Base
import Egg.Tactic.Rewrites
import Egg.Tactic.Trace
import Lean

open Lean Meta Elab Tactic

namespace Egg

-- Note: If `base? ≠ none`, the goal is an auxiliary goal and needs to be handled specially after
--       proof reconstruction.
private structure Goal where
  id    : MVarId
  type  : Congr
  base? : Option FVarId

private def getAmbientMVars : MetaM Explanation.AmbientMVars :=
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

private def genRewrites (goal : Goal) (rws : TSyntax `egg_rws) (cfg : Config) : TacticM Rewrites := do
  let mut rws ← Rewrites.parse cfg.betaReduceRws cfg.etaReduceRws rws
  if cfg.genTcProjRws then
    let tcProjTargets := #[(goal.type, Source.goal)] ++ (rws.map fun rw => (rw.toCongr, rw.src))
    rws := rws ++ (← genTcProjReductions tcProjTargets cfg.betaReduceRws cfg.etaReduceRws)
  if cfg.genTcSpecRws then
    rws := rws ++ (← genTcSpecializations rws)
  return rws

private def processRawExpl
    (rawExpl : Explanation.Raw) (goal : Goal) (rws : Rewrites) (cfg : Config.Debug)
    (amb : Explanation.AmbientMVars) : TacticM Unit := do
  withTraceNode `egg.reconstruction (fun _ => return "Result") do trace[egg.reconstruction] rawExpl
  if rawExpl.isEmpty then throwError "egg failed to prove goal"
  if cfg.exitPoint == .beforeProof then
    goal.id.admit
  else
    let expl ← rawExpl.parse
    let mut proof ← expl.proof goal.type rws amb
    -- When `goal.base? = some base`, then `proof` is a proof of `base = <goal type>`. We turn this
    -- into a proof of `<goal type>` here.
    if let some base := goal.base? then proof ← mkEqMP proof (.fvar base)
    withTraceNode `egg.reconstruction (fun _ => return "Final Proof") do
      trace[egg.reconstruction] proof
    goal.id.assign proof

open Config.Modifier (egg_cfg_mod)

elab "egg " mod:egg_cfg_mod rws:egg_rws base:(egg_base)? : tactic => do
  let goal ← getMainGoal
  let mod  ← Config.Modifier.parse mod
  let cfg := (← Config.fromOptions).modify mod
  goal.withContext do
    let amb  ← getAmbientMVars
    let goal ← parseGoal goal base
    let rws  ← genRewrites goal rws cfg
    let req  ← Request.encoding goal.type rws cfg
    req.trace
    if cfg.exitPoint == .beforeEqSat then goal.id.admit; return
    let rawExpl := req.run
    processRawExpl rawExpl goal rws cfg.toDebug amb

-- WORKAROUND: This fixes `Tests/EndOfInput`.
macro "egg" mod:egg_cfg_mod : tactic => `(tactic| egg $mod)
