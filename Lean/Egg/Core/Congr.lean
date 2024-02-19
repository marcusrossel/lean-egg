import Egg.Core.Normalize
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

-- Note: We need to instantiate mvars to reduce redundant (level) mvars which are created during
--       `forallMetaTelescopeReducing`.
--       Cf. https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/MVar.20Inclusion.20Implies.20LMVar.20Inclusion.3F
def from? (type : Expr) : MetaM (Option Congr) := do
  if let some (_, lhs, rhs) := type.eq? then
    let lhs ← instantiateMVars lhs
    let rhs ← instantiateMVars rhs
    return some { rel := .eq, lhs, rhs }
  else if let some (lhs, rhs) := type.iff? then
    let lhs ← instantiateMVars lhs
    let rhs ← instantiateMVars rhs
    return some { rel := .iff, lhs, rhs }
  else
    return none
