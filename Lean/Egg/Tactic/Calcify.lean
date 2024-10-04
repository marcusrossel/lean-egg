import Egg.Lean
import Calcify
import Lean

open Lean Meta Elab Tactic

namespace Egg

def calcify (tk : Syntax) (proof : Expr) (newFVars : Array Name) : TacticM Unit := do
  let proof ← simplify proof
  check proof
  let calcBlock ← delabProof proof
  let tactic ← if newFVars.isEmpty then
    pure calcBlock
  else
    let intros ← `(tactic|intro $[$(newFVars.map mkIdent)]*)
    mkTacticSeqPrepend intros calcBlock
  TryThis.addSuggestion tk tactic (origSpan? := ← getRef)
