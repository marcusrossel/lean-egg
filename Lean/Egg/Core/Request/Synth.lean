import Egg.Core.Explanation.Parse.Egg
import Lean
open Lean

namespace Egg

def parse (s: String) : MetaM Expr := do
  match Parser.runParserCategory (← getEnv) `egg_expr s with
  | .ok stx    =>
    let a := Explanation.parseExpr ⟨ stx ⟩
    match a with
      | .error _ => throwError "not ok"
      | .ok (c, _) => c.toExpr

  | .error _ => throwError "meh"

#reduce (types := true) MetaM PUnit
#reduce ST.Ref

@[export is_synthable]
def isSynthable (ty : String) : MetaM Bool := do
  let ty_expr ← parse ty
  let opt ← Meta.synthInstance? ty_expr
  return opt.isSome
