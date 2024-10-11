import Egg.Core.Source
import Egg.Core.Directions

open Lean

namespace Egg.Explanation

abbrev Raw := String

namespace Rewrite

structure Descriptor where
  src   : Source
  facts : Array (Option Source)
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
  -- TODO: | subst (idx : Nat) (to e : Expression)
  -- TODO: | shift (offset : Int) (cutoff : Nat) (e : Expression)
  deriving Inhabited

inductive Lemma.Justification where
  | rfl
  | symm  (lem : Nat)
  | trans (lem₁ lem₂ : Nat)
  | congr (lems : List Nat)
  | rw    (descr : Rewrite.Descriptor)
  deriving Inhabited

structure Lemma where
  lhs : Expression
  rhs : Expression
  jus : Lemma.Justification

end Explanation

-- TODO: This is not a sequence of explanation steps, but rather a tree. Should we flatten it, or
--       can we handle it as is? Might be easier to flatten, because then we can keep our remaining
--       proof reconstruction.
abbrev Explanation := Array Explanation.Lemma
