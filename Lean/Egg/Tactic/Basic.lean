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
    let some (lhs, rhs) := goalType.eqOrIff? | throwError "expected goal to be an equality or equivalence"
    let (rws, dirs) ← (← Rewrites.parse rws).withDirs (ignoreULvls := cfg.eraseULvls)
    IndexT.withFreshIndex do
      let result ← tryExplainEq lhs rhs rws dirs cfg
      withTraceNode `egg (fun _ => return m!"Goal: {← ppExpr goalType}") (collapsed := false) do
        withTraceNode `egg (fun _ => return "LHS") do trace[egg] ← lhs.toEgg! .goal cfg
        withTraceNode `egg (fun _ => return "RHS") do trace[egg] ← rhs.toEgg! .goal cfg
        withTraceNode `egg (fun _ => return (if rws.isEmpty then "No " else "") ++ "Rewrites") (collapsed := false) do
          for idx in [:rws.size], rw in rws, dir in dirs do
            withTraceNode `egg (fun _ => return m!"{idx}") do
              withTraceNode `egg (fun _ => return "LHS") do trace[egg] ← rw.lhs.toEgg! .rw cfg
              withTraceNode `egg (fun _ => return "RHS") do trace[egg] ← rw.rhs.toEgg! .rw cfg
              trace[egg] "Directions: {dir}"
        if cfg.typeTags == .indices then
          withTraceNode `egg (fun _ => return "Types") do
            let types ← IndexT.getTypes
            for idx in [:types.size], ty in types do
              withTraceNode `egg (fun _ => return m!"{idx}") (collapsed := false) do trace[egg] ty
        if !result.isEmpty then
          withTraceNode `egg (fun _ => return "Explanation") do trace[egg] result
      if result.isEmpty then
        throwError "failed to prove goal"
      else
        if cfg.buildProof then
          let expl ← Explanation.parse result
          let proof ← expl.proof rws
          goal.assign proof
        else
          goal.admit
