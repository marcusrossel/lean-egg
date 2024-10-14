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

end Rewrite

inductive Expression where
  | lvl (l : Level)
  | bvar (id : Name)
  | fvar (id : FVarId)
  | mvar (id : MVarId)
  | sort (lvl : Level)
  | const (name : Name) (lvls : List Level)
  | app (fn arg : Expression)
  | lam (var : Name) (ty body : Expression)
  | forall (var : Name) (ty body : Expression)
  | lit (l : Literal)
  | proof (prop : Expression)
  -- TODO: | subst (idx : Nat) (to e : Expression)
  -- TODO: | shift (offset : Int) (cutoff : Nat) (e : Expression)
  deriving Inhabited

inductive Justification where
  | rfl
  | symm  (lem : Nat)
  | trans (lem₁ lem₂ : Nat)
  | congr (lems : Array Nat)
  | rw    (descr : Rewrite.Descriptor)
  deriving Inhabited

structure Lemma where
  lhs : Expression
  rhs : Expression
  jus : Justification
  deriving Inhabited

end Explanation

structure Explanation where
  lemmas : Array Explanation.Lemma
  target : Explanation.Lemma
