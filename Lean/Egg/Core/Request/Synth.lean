import Egg.Core.Explanation.Parse.Egg
import Lean
open Lean

namespace Egg

def parse (s : String) : MetaM Expr := do
  match Parser.runParserCategory (← getEnv) `egg_expr s with
  | .ok stx    =>
    let a := Explanation.parseExpr ⟨ stx ⟩
    match a with
      | .error _ => throwError "not ok"
      | .ok (c, _) => c.toExpr
  | .error _ => throwError "meh"

@[export lean_is_synthable]
def isSynthable (ty : String) : MetaM Bool := do
  let tyExpr ← parse ty
  -- TODO: Is there a way to resolve the bvars?
  if tyExpr.hasLooseBVars then return false
  let inst? ← Meta.synthInstance? tyExpr
  return inst?.isSome
