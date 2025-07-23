import Egg.Core.Request.Term
import Lean
open Lean

namespace Egg

@[export lean_is_synthable]
def isSynthable (ty : String) : MetaM Bool := do
  let tyExpr ← parse ty (eagerSynth := true)
  -- TODO: Is there a way to resolve the bvars?
  if tyExpr.hasLooseBVars then return false
  let inst? ← Meta.synthInstance? tyExpr
  return inst?.isSome
