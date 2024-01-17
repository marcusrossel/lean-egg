import Lean
open Lean

namespace Egg

inductive Relation where
  | eq
  | iff

def Relation.for? (type : Expr) : Option (Relation × Expr × Expr) :=
  if let some (_, lhs, rhs) := type.eq? then
    some (.eq, lhs, rhs)
  else if let some (lhs, rhs) := type.iff? then
    some (.iff, lhs, rhs)
  else none
