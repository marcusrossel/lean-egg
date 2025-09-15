import Egg.Core.Source
import Egg.Core.Normalize
import Lean
open Lean

namespace Egg

abbrev Block := Expr

def Block.from (expr : Expr) (cfg : Config.Normalization) : MetaM Block :=
  normalize expr cfg

abbrev Blocks := Array Block
