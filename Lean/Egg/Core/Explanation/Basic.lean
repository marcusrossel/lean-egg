import Egg.Core.Source
import Egg.Core.Directions

open Lean

namespace Egg.Explanation

abbrev Raw := String

namespace Rewrite

structure Descriptor where
  src   : Source
  dir   : Direction
  facts : Array (Option Source)
  deriving Inhabited

structure Info extends Descriptor where
  pos? : Option SubExpr.Pos
  deriving Inhabited

end Rewrite

-- TODO: We can omit this type and directly parse to an `Expr`.
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
  | proof (prop : Expression)
  deriving Inhabited

structure Step extends Rewrite.Info where
  dst : Expression
  deriving Inhabited

end Explanation

structure Explanation where
  start : Explanation.Expression
  steps : Array Explanation.Step
