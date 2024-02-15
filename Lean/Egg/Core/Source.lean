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

inductive Source where
  | goal
  | explicit (idx : Nat) (eqn? : Option Nat)
  | star (id : FVarId)
  | tcProj (src : Source) (side : Side) (pos : SubExpr.Pos)
  deriving Inhabited, BEq, Hashable

namespace Source

def description : Source → String
  | goal                    => s!"⊢"
  | explicit idx none       => s!"#{idx}"
  | explicit idx (some eqn) => s!"#{idx}/{eqn}"
  | star id                 => s!"*{id.uniqueIdx!}"
  | tcProj src side pos     => s!"{src.description}[{side.description}{pos}]"

instance : ToString Source where
  toString := description
