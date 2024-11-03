import Lean
open Lean

namespace Egg.Explanation

inductive SlottedExpression where
  | bvar   (name : Name)
  | fvar   (id : FVarId)
  | mvar   (id : MVarId)
  | sort   (lvl : Level)
  | const  (name : Name) (lvls : List Level)
  | app    (var : Name) (fn arg : SlottedExpression)
  | lam    (var : Name) (ty body : SlottedExpression)
  | forall (ty body : SlottedExpression)
  | lit    (l : Literal)
  | proof  (prop : SlottedExpression)
  deriving Inhabited
