import Egg.Core.Congr
import Egg.Tactic.Base
import Lean

open Lean Meta Elab Tactic

namespace Egg

structure Goal extends Congr where private mk ::
  id : MVarId
  -- The user names of the fvars that had to be introduced in order to reach the goal congruence.
  intros : Array Name
  -- If `base? ≠ none`, the goal is an auxiliary goal and needs to be handled specially after proof
  -- reconstruction.
  base? : Option FVarId

def Goal.gen (goal : MVarId) (base? : Option <| TSyntax `egg_base) : TacticM Goal :=
  goal.withContext do
    if let some base := ← base?.mapM parseBase then
      let cgr ← Congr.from! (← mkEq (← base.getType) (← goal.getType'))
      -- TODO: In the long term it would probably be better the remove the `base?` field from `Goal`
      --       and construct a new goal mvar here and assign it to the previous goal. Then we only
      --       have to make sure to perform state reconstruction if egg fails. Perhaps we should
      --       already perform state reconstruction in that case anyway though, as we also retain
      --       introduced and renamed variables at the moment.
      return { cgr with id := goal, intros := #[], base? := base }
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
        return { cgr with id := goal, intros, base? := none }
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
