import Lean
open Lean Meta

namespace Egg

inductive Congr.Rel where
  | eq
  | iff

structure Congr where
  rel : Congr.Rel
  lhs : Expr
  rhs : Expr

namespace Congr

def Rel.mkSymm (proof : Expr) : Rel → MetaM Expr
  | eq  => mkEqSymm proof
  | iff => mkAppM ``Iff.symm #[proof]

def expr (cgr : Congr) : MetaM Expr := do
  match cgr.rel with
  | .eq  => mkEq cgr.lhs cgr.rhs
  | .iff => return mkAppN (.const `Iff []) #[cgr.lhs, cgr.rhs]

def from? (type : Expr) : Option Congr :=
  if let some (_, lhs, rhs) := type.eq? then
    some { rel := .eq, lhs, rhs }
  else if let some (lhs, rhs) := type.iff? then
    some { rel := .iff, lhs, rhs }
  else
    none

def reduced (cgr : Congr) : MetaM Congr :=
  return {
    rel := cgr.rel
    lhs := ← reduceAll cgr.lhs
    rhs := ← reduceAll cgr.rhs
  }
