import Egg.Core.Source
import Egg.Core.Normalize

open Lean Meta

namespace Egg

abbrev Block := Expr

def Block.from? (expr : Expr) (cfg : Config.Normalization) : MetaM (Option Block) := do
  unless (← inferType expr).isProp do return none
  normalize expr cfg

abbrev Blocks := Array Block
