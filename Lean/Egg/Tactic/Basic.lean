import Egg.Core.Basic
import Egg.Tactic.Config
import Egg.Tactic.Explanation.Parse
import Egg.Tactic.Explanation.Proof
import Egg.Tactic.Rewrites
import Egg.Tactic.Trace
import Lean

open Lean Meta Elab Tactic

namespace Egg

-- TODO: Egg can generate dot/svg/png-files for its e-graphs.
--       Use proof widgets to display this in the info-view.

-- TODO: Add tracing for proof reconstruction.

elab "egg " cfg:egg_cfg rws:egg_rws : tactic => do
  let goal ← getMainGoal
  let cfg ← Config.parse cfg
  goal.withContext do
    let goalType ← goal.getType'
    let some (rel, lhs, rhs) := Relation.for? goalType | throwError "expected goal to be an equality or equivalence"
    let (rws, dirs) ← (← Rewrites.parse rws).withDirs (ignoreULvls := cfg.eraseULvls)
    IndexT.withFreshIndex do
      let result ← tryExplainEq lhs rhs rws dirs cfg
      let fe := `egg.frontend
      withTraceNode fe (fun _ => return m!"Goal: {← ppExpr goalType}") do
        withTraceNode fe (fun _ => return "LHS") do trace[fe] ← lhs.toEgg! .goal cfg
        withTraceNode fe (fun _ => return "RHS") do trace[fe] ← rhs.toEgg! .goal cfg
        withTraceNode fe (fun _ => return (if rws.isEmpty then "No " else "") ++ "Rewrites") (collapsed := false) do
          for idx in [:rws.size], rw in rws, dir in dirs do
            withTraceNode fe (fun _ => return m!"{idx}") do
              withTraceNode fe (fun _ => return "LHS") do trace[fe] ← rw.lhs.toEgg! .rw cfg
              withTraceNode fe (fun _ => return "RHS") do trace[fe] ← rw.rhs.toEgg! .rw cfg
              trace[fe] "Directions: {dir}"
        if cfg.typeTags == .indices then
          withTraceNode fe (fun _ => return "Types") do
            let types ← IndexT.getTypes
            for idx in [:types.size], ty in types do
              withTraceNode fe (fun _ => return m!"{idx}") (collapsed := false) do trace[fe] ty
      if result.isEmpty then
        throwError "failed to prove goal"
      else
        withTraceNode `egg.reconstruction (fun _ => return "Explanation") do trace[egg.reconstruction] result
        if cfg.buildProof then
          let expl ← Explanation.parse result
          let proof ← expl.proof rel rws
          goal.assign proof
        else
          goal.admit
