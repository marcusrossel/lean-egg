import Egg.Lean
import Lean
open Lean

namespace Egg

inductive Source where
  | goal
  | explicit (idx : Nat) (eqn? : Option Nat)
  | star (id : FVarId)
  | tcProj (src : Source) (idx : Nat)
  deriving Inhabited, BEq, Hashable

namespace Source

def description : Source → String
  | .goal                    => s!"⊢"
  | .explicit idx none       => s!"#{idx}"
  | .explicit idx (some eqn) => s!"#{idx}/{eqn}"
  | .star id                 => s!"*{id.uniqueIdx!}"
  | .tcProj src idx          => s!"{src.description}[{idx}]"

instance : ToString Source where
  toString := description
