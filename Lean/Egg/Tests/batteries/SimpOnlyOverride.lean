import Lean
import Egg
open Lean Meta Elab Parser Tactic

elab_rules : tactic
  | `(simp| simp only $[[$lemmas:simpLemma,*]]?) => do
    let simpStx ← if let some lems := lemmas then `(tactic| simp only [$lems,*]) else `(tactic| simp only)
    let mut args ← simpOnlyBuiltins.toArray.mapM fun b => `(egg_arg|$(mkIdent b):ident)
    if let some lems := lemmas then
      for lem in lems.getElems do
        -- syntax simpLemma := (simpPre <|> simpPost)? patternIgnore("← " <|> "<- ")? term
        let lemTerm : Term := ⟨lem.raw[2]⟩
        args := args.push <| ← `(egg_arg|$lemTerm:term)
    focus do
      let s ← saveState
      let goal ← getMainGoal
      evalSimp simpStx
      unless (← getGoals).isEmpty do return
      let some _ ← Egg.Congr.from? (← Egg.normalize (← goal.getType) .noReduce) | return
      s.restore
      try
        evalTactic (← `(tactic|egg [$args,*]))
        logWarning "egg succeeded"
      catch err =>
        s.restore
        logWarning m!"egg failed: {err.toMessageData}"
        evalSimp simpStx
