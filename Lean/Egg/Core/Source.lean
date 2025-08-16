import Egg.Core.Direction
import Egg.Lean
import Lean
open Lean

namespace Egg

inductive Source.NatLit where
  | zero
  | toSucc
  | ofSucc
  | add
  | sub
  | mul
  | pow
  | div
  | mod
deriving Inhabited, BEq, Hashable, Repr

inductive Source.Level where
  | maxSucc
  | maxComm
  | imaxZero
  | imaxSucc
deriving Inhabited, BEq, Hashable, Repr

inductive Source.TcProjLocation where
  | root
  | left
  | right
  | cond (idx : Nat)
deriving Inhabited, BEq, Hashable, Repr

inductive Source.SubstShift where
  | bvar
  | app
  | lam
  | forall
  | fvar
  | mvar
  | sort
  | lit
  | proof
  | inst
  | unknown
  | abort
deriving Inhabited, BEq, Hashable, Repr

inductive Source where
  | goal
  | intro (idx : Nat)
  | guide (idx : Nat) (derived : Bool)
  | explicit (idx : Nat) (eqn? : Option Nat)
  | star (id : FVarId)
  | ground (src : Source)
  | reifiedEq
  | factAnd
  | structProj (idx : Nat)
  | goalTypeSpec (src : Source) (idx : Nat)
  | tcProj (src : Source) (loc : Source.TcProjLocation) (pos : SubExpr.Pos) (depth : Nat)
  | explosion (src : Source) (loc : List Nat)
  | natLit (src : Source.NatLit)
  | subst (src : Source.SubstShift)
  | shift (src : Source.SubstShift)
  | eta (expansion : Bool)
  | beta
  | level (src : Source.Level)
  | builtin (idx : Nat)
  | tagged (name : Name) (eqn? : Option Nat)
deriving Inhabited, BEq, Hashable, Repr

namespace Source

def NatLit.description : NatLit → String
  | zero   => "≡0"
  | toSucc => "≡→S"
  | ofSucc => "≡S→"
  | add    => "≡+"
  | sub    => "≡-"
  | mul    => "≡*"
  | pow    => "≡^"
  | div    => "≡/"
  | mod    => "≡%"

def Level.description : Level → String
  | maxSucc  => "≡maxS"
  | maxComm  => "≡max↔"
  | imaxZero => "≡imax0"
  | imaxSucc => "≡imaxS"

def TcProjLocation.description : TcProjLocation → String
  | root     => "▪"
  | left     => "◂"
  | right    => "▸"
  | cond idx => s!"{idx}?"

def SubstShift.description : SubstShift → String
  | bvar    => "bvar"
  | app     => "app"
  | lam     => "λ"
  | .forall => "∀"
  | fvar    => "fvar"
  | mvar    => "mvar"
  | sort    => "sort"
  | lit     => "lit"
  | proof   => "proof"
  | inst    => "inst"
  | unknown => "_"
  | abort   => "|"

-- Note: It's important that we remove the whitespace from the list in the `.explosion` case,
--       because otherwise egg adds quotes around the rule name.
def description : Source → String
  | goal                    => "⊢"
  | intro idx               => s!"▰{idx}"
  | guide idx derived       => s!"↣{idx}{if derived then "!" else ""}"
  | explicit idx none       => s!"#{idx}"
  | explicit idx (some eqn) => s!"#{idx}/{eqn}"
  | star id                 => s!"∗{id.uniqueIdx!}"
  | ground src              => s!"{src.description}↓"
  | reifiedEq               => "="
  | factAnd                 => "∧"
  | structProj idx          => s!"▵{idx}"
  | goalTypeSpec src idx    => s!"{src.description}<{idx}⊢>"
  | tcProj src loc pos dep  => s!"{src.description}[{loc.description}{pos.asNat},{dep}]"
  | explosion src loc       => s!"{src.description}💥{(toString loc).replace " " ""}"
  | natLit src              => src.description
  | subst src               => s!"↦{src.description}"
  | shift src               => s!"↑{src.description}"
  | eta false               => "≡η"
  | eta true                => "≡η+"
  | beta                    => "≡β"
  | level src               => src.description
  | builtin idx             => s!"◯{idx}"
  | tagged name none        => s!"□{name}"
  | tagged name (some eqn)  => s!"□{name}/{eqn}"

instance : ToString Source where
  toString := description

instance : Ord Source where
  compare src₁ src₂ := compare src₁.description src₂.description

def isDefEq : Source → Bool
  | natLit _ | eta _ | beta | level _ | subst _ | shift _ | structProj _ => true
  | _                                                                    => false

def containsTcProj : Source → Bool
  | tcProj ..                                          => true
  | ground src | goalTypeSpec src _ | explosion src .. => containsTcProj src
  | _                                                  => false

def isNatLitConversion : Source → Bool
  | natLit .zero | natLit .toSucc | natLit .ofSucc => true
  | _                                              => false

def isSubst : Source → Bool
  | subst _ => true
  | _       => false

def involvesBinders : Source → Bool
  | subst _ | shift _ | eta _ | beta => true
  | _                                => false

def isReifiedEq : Source → Bool
  | reifiedEq => true
  | _         => false

def isGround : Source → Bool
  | ground _ => true
  | _        => false
