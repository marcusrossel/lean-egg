import Egg.Core.Congr
import Egg.Lean
import Lean

open Lean Meta Elab Tactic

namespace Egg

structure Goal extends Congr where private mk ::
  id : MVarId
  -- The user names of the fvars that had to be introduced in order to reach the goal congruence.
  intros : Array Name

def Goal.gen (goal : MVarId) : TacticM Goal :=
  goal.withContext do
    let goal ← getMainGoal
    let goalType ← withReducible goal.getType'
    let goalTypeType ← inferType goalType
    unless goalTypeType.isProp do
      throwError m!"goal type is not a proposition:\n {goalType} : {goalTypeType}"
    let fvars := (← getLCtx).getFVarIds
    withReducible do evalTactic <| ← `(tactic|repeat intro)
    let goal ← getMainGoal
    let (goal, intros) ← genIntros goal fvars
    goal.withContext do
      let goalType ← withReducible goal.getType'
      if let some cgr ← Congr.from? goalType then
        return { cgr with id := goal, intros }
      else
        let goalEqTrue  ← mkEq goalType (.const ``True [])
        let mGoalEqTrue ← mkFreshExprMVar goalEqTrue
        let oldProof    ← mkOfEqTrue mGoalEqTrue
        goal.assignIfDefeq' oldProof
        let cgr ← Congr.from! goalEqTrue
        return { cgr with id := mGoalEqTrue.mvarId!, intros }
where
  genIntros (goal : MVarId) (previousFVars : Array FVarId) : MetaM (MVarId × Array Name) := do
    goal.withContext do
      let mut goal := goal
      let mut intros := #[]
      let newFVars := (← getLCtx).getFVarIds.filter (!previousFVars.contains ·)
      for fvar in newFVars do
        let (g, name) ← goal.withContext do
          let userName := (← getLCtx).getUnusedName (← fvar.getUserName)
          pure (← goal.rename fvar userName, userName)
        goal := g
        intros := intros.push name
      return (goal, intros)
