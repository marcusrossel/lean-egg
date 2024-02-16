import Egg.Core.Request
import Egg.Core.Explanation.Proof
import Egg.Core.Gen.TcProjs
import Egg.Tactic.Config
import Egg.Tactic.Explanation
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

private abbrev M := ReaderT M.State TacticM

private def parseGoal (goal : MVarId) (base? : Option (TSyntax `egg_base)) :
    MetaM M.State.Goal := do
  let goalType ← normalize (← goal.getType')
  let base? ← base?.mapM parseBase
  let cgr ← getCongr goalType base?
  return { id := goal, type := cgr, base? }
where
  getCongr (goalType : Expr) (base? : Option FVarId) : MetaM Congr := do
    if let some base := base? then
      return { lhs := ← base.getType, rhs := goalType, rel := .eq : Congr }
    else if let some c := Congr.from? goalType then
      return c
    else
      throwError "expected goal to be of type '=' or '↔', but found:\n{← ppExpr goalType}"

private def genRewrites (goal : M.State.Goal) (rws : TSyntax `egg_rws) (cfg : Config) :
    TacticM Rewrites := do
  let mut rws ← Rewrites.parse rws
  unless cfg.genTcProjRws do return rws
  let targets := #[(goal.type, Source.goal)] ++ (rws.map fun rw => (rw.toCongr, rw.src))
  return rws ++ (← genTcProjReductions targets)

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
      trace[egg.frontend] ← encode (← goal).type.lhs .goal cfg
    withTraceNode `egg.frontend (fun _ => return "RHS") do
      trace[egg.frontend] ← encode (← goal).type.rhs .goal cfg
    withTraceNode `egg.frontend (fun _ => return (if rws.isEmpty then "No " else "") ++ "Rewrites") (collapsed := false) do
      for rw in rws, dir in (← dirs) do
        withTraceNode `egg.frontend (fun _ => return m!"{rw.src}") do
          withTraceNode `egg.frontend (fun _ => return "LHS") do
            trace[egg.frontend] ← encode rw.lhs rw.src cfg
          withTraceNode `egg.frontend (fun _ => return "RHS") do
            trace[egg.frontend] ← encode rw.rhs rw.src cfg
          trace[egg.frontend] "Directions: {dir}"
      if cfg.genNatLitRws then
        trace[egg.frontend] "Nat Literal Conversions"

private def processRawExpl (rawExpl : Explanation.Raw) : M Unit := do
  if rawExpl.isEmpty then throwError "egg failed to prove goal"
  withTraceNode `egg.reconstruction (fun _ => return "Result") do trace[egg.reconstruction] rawExpl
  let cfg ← cfg
  let goal ← goal
  if cfg.exitPoint == .beforeProof then
    goal.id.admit
  else
    let expl ← rawExpl.parse
    let mut proof ← expl.proof goal.type (← rws)
    -- When `goal.base? = some base`, then `proof` is a proof of `base = <goal type>`. We turn this
    -- into a proof of `<goal type>` here.
    if let some base := goal.base? then proof ← mkEqMP proof (.fvar base)
    goal.id.assign proof

def mkRequest : M Request := do
  Request.encoding (← goal).type (← rws) (← dirs) (← cfg)

def run (s : M.State) (m : M α) : TacticM α :=
  m.run s

end M

open M

-- TODO: When constructing the `dirs`, there is a mismatch between `ignoreULvls` and
--       `eraseConstLevels` when it comes to `Expr.sort`. This might cause egg to crash due to
--       unbound mvars.
elab "egg " cfg:egg_cfg rws:egg_rws base:(egg_base)? : tactic => do
  let goal ← getMainGoal
  let cfg ← Config.parse cfg
  goal.withContext do
    let goal ← parseGoal goal base
    let rws ← genRewrites goal rws cfg
    let dirs ← rws.validDirs! (ignoreULvls := cfg.eraseConstLevels)
    run { goal, cfg, rws, dirs } do
      let request ← mkRequest
      traceFrontend
      if cfg.exitPoint == .beforeEqSat then goal.id.admit; return
      let rawExpl := request.run
      processRawExpl rawExpl
