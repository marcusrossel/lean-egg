import Egg.Core.Congr
import Egg.Tactic.Base
import Egg.Lean
import Lean

open Lean Meta Elab Tactic

namespace Egg

structure Goal extends Congr where private mk ::
  id : MVarId
  -- The user names of the fvars that had to be introduced in order to reach the goal congruence.
  intros : Array Name

def Goal.gen (goal : MVarId) (base? : Option <| TSyntax `egg_base) : TacticM Goal :=
  goal.withContext do
    if let some base := ← base?.mapM parseBase then
      let eq ← mkEq (← base.getType) (← goal.getType)
      let newGoal ← mkFreshExprMVar eq
      let oldProof ← mkEqMP newGoal (.fvar base)
      goal.assignIfDefeq' oldProof
      let cgr ← Congr.from! eq
      return { cgr with id := newGoal.mvarId!, intros := #[] }
    else
      let fvars := (← getLCtx).getFVarIds
      evalTactic <| ← `(tactic|repeat intro)
      let goal ← getMainGoal
      goal.withContext do
        let (goal, intros) ← genIntros goal fvars
        let goalType ← goal.getType'
        let some cgr ← Congr.from? goalType
          | throwError "expected goal to be of type '=', '↔', '∀ ..., _ = _', or '∀ ..., _ ↔ _', \
                        but found:\n\n  {← ppExpr goalType}"
        return { cgr with id := goal, intros }
where
  genIntros (goal : MVarId) (previousFVars : Array FVarId) : MetaM (MVarId × Array Name) := do
    let mut goal := goal
    let mut intros := #[]
    let newFVars := (← getLCtx).getFVarIds.filter (!previousFVars.contains ·)
    for fvar in newFVars do
      let usableName := (← fvar.getUserName).eraseMacroScopes
      intros := intros.push usableName
      goal ← goal.rename fvar usableName
    return (goal, intros)
