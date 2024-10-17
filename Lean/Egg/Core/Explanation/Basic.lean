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
  | lvl (l : Level)
  deriving Inhabited

def Expression.toString : Expression → String
  | .bvar id            => s!"{id}"
  | fvar id             => s!"{id.name}"
  | mvar id             => s!"{id.name}"
  | sort l              => s!"(sort {l})"
  | const name lvls     => s!"(const {name} {lvls})"
  | app fn arg          => s!"(app {toString fn} {toString arg})"
  | lam var ty body     => s!"(λ {var} {toString ty} {toString body})"
  | .forall var ty body => s!"(∀ {var} {toString ty} {toString body})"
  | lit (.natVal n)     => s!"{n}"
  | lit (.strVal s)     => s!"\"{s}\""
  | proof prop          => s!"(? : {toString prop})"
  | .lvl l              => s!"{l}"

inductive Justification where
  | rfl
  | symm  (lem : Nat)
  | trans (lem₁ lem₂ : Nat)
  | congr (lems : Array Nat)
  | rw    (descr : Rewrite.Descriptor)
  deriving Inhabited

def Justification.toString : Justification → String
  | rfl         => "rfl"
  | symm l      => s!"symm {l}"
  | trans l₁ l₂ => s!"trans {l₁} {l₂}"
  | congr lems  => s!"congr {lems}"
  | rw descr    => s!"rw {descr.src.description}"

structure Lemma where
  lhs : Expression
  rhs : Expression
  jus : Justification
  deriving Inhabited

def Lemma.toString (lem : Lemma) : String :=
  s!"{lem.lhs.toString} = {lem.rhs.toString} by {lem.jus.toString}"

structure Tree where
  lemmas : Std.HashMap Nat Explanation.Lemma
  target : Nat

def Tree.targetLemma (expl : Tree) : Explanation.Lemma :=
  expl.lemmas[expl.target]!

def Tree.toString (expl : Tree) : String := Id.run do
  let mut str := ""
  for (idx, lem) in expl.lemmas do
    let sep := if idx == expl.target then "" else "\n\n"
    str := s!"{str}[{idx}]: {lem.toString}{sep}"
  return str
