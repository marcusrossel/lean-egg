import Egg.Core.Source
import Egg.Core.Rewrites.Directions

open Lean
open Egg.Rewrite (Direction)

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

inductive Lvl where
  | zero
  | succ (lvl : Lvl)
  | max (lhs rhs : Lvl)
  | imax (lhs rhs : Lvl)
  | param (n : Name)
  | mvar (id : LMVarId)
  | explosion
  deriving Inhabited

inductive Expression where
  | bvar (idx : Nat)
  | fvar (id : FVarId)
  | mvar (id : MVarId)
  | sort (lvl : Lvl)
  | const (name : Name) (lvls : List Lvl)
  | app (fn arg : Expression)
  | lam (ty body : Expression)
  | forall (ty body : Expression)
  | lit (l : Literal)
  | explosion
  | erased
  deriving Inhabited

structure Step extends Rewrite.Info where
  dst : Expression
  deriving Inhabited

end Explanation

structure Explanation where
  start : Explanation.Expression
  steps : Array Explanation.Step
