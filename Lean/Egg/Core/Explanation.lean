import Egg.Core.Rewrites

open Lean
open Egg.Rewrite (Direction)

namespace Egg.Explanation.Rewrite

structure Descriptor where
  src : Rewrite.Source
  dir : Direction
  deriving Inhabited

structure Info extends Descriptor where
  pos : SubExpr.Pos
  deriving Inhabited

end Rewrite

inductive Expression where
  | bvar (idx : Nat)
  | fvar (id : FVarId)
  | mvar (id : MVarId)
  | sort (lvl : Level)
  | const (name : Name) (lvls : Array Level)
  | app (fn arg : Expression)
  | lam (body : Expression)
  | forall (type body : Expression)
  | lit (l : Literal)
  deriving Inhabited

structure Step extends Rewrite.Info where
  dst : Expression
  deriving Inhabited

end Explanation

structure Explanation where
  start : Explanation.Expression
  steps : Array Explanation.Step
