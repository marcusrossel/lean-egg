import Lean
open Lean Meta

namespace Egg

-- Performs ζ-reduction, converts `Expr.proj`s to `Expr.app`s and removes `Expr.mdata`s.
partial def normalize : Expr → MetaM Expr
  | .mdata _ e        => normalize e
  | .app fn arg       => return .app (← normalize fn) (← normalize arg)
  | .lam n ty b i     => do
    withLocalDecl n i (← normalize ty) fun fvar => do
      mkLambdaFVars #[fvar] (← normalize <| b.instantiate1 fvar)
  | .forallE n ty b i => do
    withLocalDecl n i (← normalize ty) fun fvar => do
      mkForallFVars #[fvar] (← normalize <| b.instantiate1 fvar)
  | e@(.letE ..)      => do normalize (← zetaReduce e)
  | .proj ty ctor b   => do normalize (← expandProj ty ctor b)
  | e                 => return e
where
  expandProj (ty : Name) (ctor : Nat) (b : Expr) : MetaM Expr := do
    let some field := (getStructureFields (← getEnv) ty)[ctor]? | throwError "'Egg.normalize' failed to reduce proj"
    mkProjection b field
