import Egg.Core.Basic
import Egg.Tactic.Config
import Egg.Tactic.Explanation.Parse
import Egg.Tactic.Explanation.Proof
import Egg.Tactic.Rewrites
import Egg.Tactic.Trace
import Lean

open Lean Meta Elab Tactic

namespace Egg

-- TODO: Not super happy with the `M` monad.

private structure M.State.Goal where
  ref  : MVarId
  type : Congr

private structure M.State where
  goal  : State.Goal
  cfg   : Config
  rws   : Rewrites
  dirs  : Array Rewrite.Directions

private abbrev M := ReaderT M.State <| IndexT <| TacticM

private def parseGoal (goal : MVarId) (reduce : Bool) : MetaM M.State.Goal := do
  let type ← goal.getType'
  let some cgr := Congr.from? type | throwError "expected goal to be an equality or equivalence"
  return {
    ref := goal
    type := if reduce then ← cgr.reduced else cgr
  }

private def parseRws (rws : TSyntax `egg_rws) (cfg : Config) :
    TacticM (Rewrites × Array Rewrite.Directions) := do
  let parsed ← Rewrites.parse cfg.reduce rws
  parsed.withDirs (ignoreULvls := cfg.eraseULvls)

namespace M

private def goal : M State.Goal                 := State.goal <$> read
private def cfg  : M Config                     := State.cfg  <$> read
private def rws  : M Rewrites                   := State.rws  <$> read
private def dirs : M (Array Rewrite.Directions) := State.dirs <$> read

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
  unless !result.isEmpty do throwError "failed to prove goal"
  withTraceNode `egg.reconstruction (fun _ => return "Explanation") do
    trace[egg.reconstruction] result
  let cfg ← cfg
  let goal ← goal
  if cfg.buildProof then
    let expl ← Explanation.parse result
    let proof ← expl.proof goal.type (← rws) cfg
    goal.ref.assign proof
  else
    goal.ref.admit

def run (s : M.State) (m : M α) : IndexT TacticM α :=
  m.run s

end M

elab "egg " cfg:egg_cfg rws:egg_rws : tactic => do
  let goal ← getMainGoal
  let cfg ← Config.parse cfg
  goal.withContext do
    let goal ← parseGoal goal cfg.reduce
    let (rws, dirs) ← parseRws rws cfg
    IndexT.withFreshIndex do
      M.run { goal, cfg, rws, dirs } do
        let result ← explainCongr goal.type rws dirs cfg
        M.traceFrontend
        M.processResult result
