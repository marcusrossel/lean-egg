import Egg.Core.Directions
import Egg.Lean
import Lean
open Lean

namespace Egg

inductive Side where
  | left
  | right
  deriving Inhabited, BEq, Hashable

def Side.description : Side → String
  | left => "l"
  | right => "r"

def Side.isLeft : Side → Bool
  | left  => true
  | right => false

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

inductive Source where
  | goal
  | explicit (idx : Nat) (eqn? : Option Nat)
  | star (id : FVarId)
  | tcProj (src : Source) (side : Side) (pos : SubExpr.Pos)
  | tcSpec (src : Source) (dir : Direction)
  | natLit (src : Source.NatLit)
  | eta
  | beta
  deriving Inhabited, BEq, Hashable

namespace Source

def NatLit.description : Source.NatLit → String
  | zero   => "≡0"
  | toSucc => "≡→S"
  | ofSucc => "≡S→"
  | add    => "≡+"
  | sub    => "≡-"
  | mul    => "≡*"
  | pow    => "≡^"
  | div    => "≡/"
  | mod    => "≡%"

def description : Source → String
  | goal                    => "⊢"
  | explicit idx none       => s!"#{idx}"
  | explicit idx (some eqn) => s!"#{idx}/{eqn}"
  | star id                 => s!"*{id.uniqueIdx!}"
  | tcProj src side pos     => s!"{src.description}[{side.description}{pos}]"
  | tcSpec src dir          => s!"{src.description}<{dir.description}>"
  | natLit src              => src.description
  | eta                     => "≡η"
  | beta                    => "≡β"

instance : ToString Source where
  toString := description

def isDefEq : Source → Bool
  | natLit _ | eta | beta => true
  | _                     => false
