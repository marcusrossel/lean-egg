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

inductive Source.NatLit where
  | zero
  | toSucc
  | ofSucc
  deriving Inhabited, BEq, Hashable

mutual

inductive Source.Explosion where
  | exprSubst (idx : Nat)
  | lvlSubst (idx : Nat)
  | rw (src : Source) (side : Side)

inductive Source where
  | goal
  | explicit (idx : Nat) (eqn? : Option Nat)
  | star (id : FVarId)
  | tcProj (src : Source) (side : Side) (pos : SubExpr.Pos)
  | explosion (src : Source.Explosion)
  | natLit (src : Source.NatLit)
  deriving Inhabited, BEq, Hashable

end

namespace Source

def NatLit.description : Source.NatLit → String
  | zero   => s!"!z"
  | toSucc => s!"!t"
  | ofSucc => s!"!o"

mutual

def Explosion.description : Explosion → String
  | .exprSubst idx => s!"e<{idx}>"
  | .lvlSubst idx  => s!"l<{idx}>"
  | .rw src side   => s!"{src.description}<{side.description}>"

def description : Source → String
  | goal                    => s!"⊢"
  | explicit idx none       => s!"#{idx}"
  | explicit idx (some eqn) => s!"#{idx}/{eqn}"
  | star id                 => s!"*{id.uniqueIdx!}"
  | tcProj src side pos     => s!"{src.description}[{side.description}{pos}]"
  | explosion src           => src.description
  | natLit src              => src.description

end

instance : ToString Source where
  toString := description

def isNatLit : Source → Bool
  | natLit _ => true
  | _        => false
