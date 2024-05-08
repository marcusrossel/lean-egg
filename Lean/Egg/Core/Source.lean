import Egg.Core.Directions
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
  deriving Inhabited, BEq, Hashable

inductive Source.Level where
  | maxSucc
  | maxComm
  | imaxZero
  | imaxSucc
  deriving Inhabited, BEq, Hashable

inductive Source.TcProjLocation where
  | root
  | left
  | right
  | cond (idx : Nat)
  deriving Inhabited, BEq, Hashable

inductive Source where
  | goal
  | guide (idx : Nat)
  | explicit (idx : Nat) (eqn? : Option Nat)
  | star (id : FVarId)
  | fact (src : Source)
  | tcProj (src : Source) (loc : Source.TcProjLocation) (pos : SubExpr.Pos)
  | tcSpec (src : Source) (dir : Directions)
  | natLit (src : Source.NatLit)
  | eta
  | beta
  | level (src : Source.Level)
  | builtin (idx : Nat)
  deriving Inhabited, BEq, Hashable

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

def description : Source → String
  | goal                    => "⊢"
  | guide idx               => s!"↣{idx}"
  | explicit idx none       => s!"#{idx}"
  | explicit idx (some eqn) => s!"#{idx}/{eqn}"
  | star id                 => s!"*{id.uniqueIdx!}"
  | fact src                => s!"!{src.description}"
  | tcProj src loc pos      => s!"{src.description}[{loc.description}{pos.asNat}]"
  | tcSpec src dirs         => s!"{src.description}<{dirs.description}>"
  | natLit src              => src.description
  | eta                     => "≡η"
  | beta                    => "≡β"
  | level src               => src.description
  | builtin idx             => s!"◯{idx}"

instance : ToString Source where
  toString := description

def isRewrite : Source → Bool
  | goal | guide _ => false
  | _              => true

def isDefEq : Source → Bool
  | natLit _ | eta | beta | level _ => true
  | _                               => false

def containsTcProj : Source → Bool
  | tcProj ..     => true
  | tcSpec src .. => src.containsTcProj
  | _             => false

def isNatLitConversion : Source → Bool
  | .natLit .zero | .natLit .toSucc | .natLit .ofSucc => true
  | _                                                 => false
