import Egg.Core.Source
import Egg.Core.Directions

open Lean

namespace Egg.Explanation

abbrev Raw := String

namespace Rewrite

structure Descriptor where
  src : Source
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
  | const (name : Name) (lvls : List Level)
  | app (fn arg : Expression)
  | lam (ty body : Expression)
  | forall (ty body : Expression)
  | lit (l : Literal)
  | erased
  deriving Inhabited

structure Step extends Rewrite.Info where
  dst : Expression
  deriving Inhabited

end Explanation

structure Explanation where
  start : Explanation.Expression
  steps : Array Explanation.Step
