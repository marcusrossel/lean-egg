import Lean
open Lean Meta

namespace Egg

-- Performs ζ-reduction, converts `Expr.proj`s to `Expr.app`s and removes `Expr.mdata`s.
-- Note that normalization does not affect binders' type expressions.
partial def normalize : Expr → MetaM Expr
  | .mdata _ e        => normalize e
  | .app fn arg       => return .app (← normalize fn) (← normalize arg)
  | .lam n ty b i     => return .lam n ty (← normalize b) i
  | .forallE n ty b i => return .forallE n ty (← normalize b) i
  | e@(.letE ..)      => do normalize (← zetaReduce e)
  | .proj ty ctor b   => do normalize (← expandProj ty ctor b)
  | e                 => return e
where
  expandProj (ty : Name) (ctor : Nat) (b : Expr) : MetaM Expr := do
    let some field := (getStructureFields (← getEnv) ty)[ctor]? | throwError "'Egg.normalize' failed to reduce proj"
    mkProjection b field
