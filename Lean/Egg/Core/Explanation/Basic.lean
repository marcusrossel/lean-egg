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
  | bvar (id : String)
  | fvar (id : FVarId)
  | mvar (id : MVarId)
  | sort (lvl : Level)
  | const (name : Name) (lvls : List Level)
  | app (fn arg : Expression)
  | lam (var : String) (ty body : Expression)
  | forall (var : String) (ty body : Expression)
  | lit (l : Literal)
  | proof (prop : Expression)
  | lvl (l : Level)
  deriving Inhabited

def Expression.toString : Expression → (pretty : Bool := false) → String
  | bvar id            , false => s!"${id}"
  | bvar id            , true  => s!"b#{id}"
  | fvar id            , false => s!"(fvar {id.name})"
  | fvar id            , true  => s!"f#{id.name}"
  | mvar id            , false => s!"(mvar {id.name})"
  | mvar id            , true  => s!"m#{id.name}"
  | sort l             , false => s!"(sort {l})"
  | sort l             , true  => s!"Sort {l}"
  | const name lvls    , false => s!"(const {name} {lvls})"
  | const name _       , true  => s!"{name}"
  | app fn arg         , false => s!"(app {toString fn false} {toString arg false})"
  | app fn arg         , true  => s!"({toString fn true} {toString arg true})"
  | lam var ty body    , false => s!"(λ ${var} {toString ty false} {toString body false})"
  | lam var ty body    , true  => s!"(λ {var} : {toString ty true} => {toString body true})"
  | .forall var ty body, false => s!"(∀ ${var} {toString ty false} {toString body false})"
  | .forall var ty body, true  => s!"(∀ {var} : {toString ty true} => {toString body true})"
  | lit (.natVal n)    , _     => s!"{n}"
  | lit (.strVal s)    , _     => s!"\"{s}\""
  | proof prop         , py    => s!"(? : {toString prop py})"
  | .lvl l             , _     => s!"{l}"

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

def Lemma.toString (lem : Lemma) (pretty := false) : String :=
  s!"{lem.lhs.toString pretty} = {lem.rhs.toString pretty} by {lem.jus.toString}"

structure Tree where
  lemmas : Std.HashMap Nat Explanation.Lemma
  target : Nat

def Tree.targetLemma (expl : Tree) : Explanation.Lemma :=
  expl.lemmas[expl.target]!

def Tree.toString (expl : Tree) (pretty := false) : String := Id.run do
  let mut str := ""
  for (idx, lem) in expl.lemmas do
    let sep := if idx == expl.target then "" else "\n\n"
    str := s!"{str}[{idx}]: {lem.toString pretty}{sep}"
  return str
