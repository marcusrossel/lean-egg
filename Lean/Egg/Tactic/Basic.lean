import Egg.Core.Basic
import Egg.Tactic.Config
import Egg.Tactic.Explanation.Parse
import Egg.Tactic.Explanation.Proof
import Egg.Tactic.Base
import Egg.Tactic.Rewrites
import Egg.Tactic.Trace
import Lean

open Lean Meta Elab Tactic

namespace Egg

-- TODO: Not super happy with the `M` monad.

-- Note: If `base? ≠ none`, the goal is an auxiliary goal and needs to be handled specially after
--       proof reconstruction.
private structure M.State.Goal where
  id    : MVarId
  type  : Congr
  base? : Option FVarId

private structure M.State where
  goal : State.Goal
  cfg  : Config
  rws  : Rewrites
  dirs : Array Rewrite.Directions

private abbrev M := ReaderT M.State <| IndexT <| TacticM

private def parseGoal (goal : MVarId) (reduce : Bool) (base? : Option (TSyntax `egg_base)) :
    MetaM M.State.Goal := do
  let goalType ← goal.getType'
  let base? ← base?.mapM parseBase
  let c ← getCongr goalType base?
  let cgr := if reduce then ← c.reduced else c
  return { id := goal, type := cgr, base? }
where
  getCongr (goalType : Expr) (base? : Option FVarId) : MetaM Congr := do
    if let some base := base? then
      return { lhs := ← base.getType, rhs := goalType, rel := .eq : Congr }
    else if let some c := Congr.from? goalType then
      return c
    else
      throwError "expected goal to be of type '=' or '↔', but found:\n{← ppExpr goalType}"

private def parseRws (rws : TSyntax `egg_rws) (cfg : Config) :
    TacticM (Rewrites × Array Rewrite.Directions) := do
  let parsed ← Rewrites.parse cfg.reduce rws
  parsed.withDirs (ignoreULvls := cfg.eraseULvls)

namespace M

private def goal  : M State.Goal                 := State.goal  <$> read
private def cfg   : M Config                     := State.cfg   <$> read
private def rws   : M Rewrites                   := State.rws   <$> read
private def dirs  : M (Array Rewrite.Directions) := State.dirs  <$> read

private def traceFrontend : M Unit := do
  let cfg ← cfg
  let rws ← rws
  let goalType ← (← goal).type.expr
  withTraceNode `egg.frontend (fun _ => return m!"Goal: {← ppExpr goalType}") do
    withTraceNode `egg.frontend (fun _ => return "LHS") do
      trace[egg.frontend] ← (← goal).type.lhs.toEgg! .goal cfg
    withTraceNode `egg.frontend (fun _ => return "RHS") do
      trace[egg.frontend] ← (← goal).type.rhs.toEgg! .goal cfg
    withTraceNode `egg.frontend (fun _ => return (if rws.isEmpty then "No " else "") ++ "Rewrites") (collapsed := false) do
      for idx in [:rws.size], rw in rws, dir in (← dirs) do
        withTraceNode `egg.frontend (fun _ => return m!"{idx}") do
          withTraceNode `egg.frontend (fun _ => return "LHS") do
            trace[egg.frontend] ← rw.lhs.toEgg! .rw cfg
          withTraceNode `egg.frontend (fun _ => return "RHS") do
            trace[egg.frontend] ← rw.rhs.toEgg! .rw cfg
          trace[egg.frontend] "Directions: {dir}"
    if cfg.typeTags == .indices then
      withTraceNode `egg.frontend (fun _ => return "Types") do
        let types ← IndexT.getTypes
        for idx in [:types.size], ty in types do
          withTraceNode `egg.frontend (fun _ => return m!"{idx}") (collapsed := false) do
            trace[egg.frontend] ty

private def processResult (result : String) : M Unit := do
  unless !result.isEmpty do throwError "egg failed to prove goal"
  withTraceNode `egg.reconstruction (fun _ => return "Result") do trace[egg.reconstruction] result
  let cfg ← cfg
  let goal ← goal
  if cfg.exitPoint == .beforeProof then
    goal.id.admit
  else
    let expl ← Explanation.parse result
    let mut proof ← expl.proof goal.type (← rws) cfg
    -- When `goal.base? = some base`, then `proof` is a proof of `base = <goal type>`. We turn this
    -- into a proof of `<goal type>` here.
    if let some base := goal.base? then proof ← mkEqMP proof (.fvar base)
    goal.id.assign proof

def runEgg : M String := do
  explainCongr (← goal).type (← rws) (← dirs) (← cfg)

def runWithFreshIndex (s : M.State) (m : M α) : TacticM α :=
  IndexT.withFreshIndex (m.run s)

end M

open M

elab "egg " cfg:egg_cfg rws:egg_rws base:(egg_base)? : tactic => do
  let goal ← getMainGoal
  let cfg ← Config.parse cfg
  goal.withContext do
    let goal ← parseGoal goal cfg.reduce base
    let (rws, dirs) ← parseRws rws cfg
    runWithFreshIndex { goal, cfg, rws, dirs } do
      let result ← runEgg
      traceFrontend
      processResult result
