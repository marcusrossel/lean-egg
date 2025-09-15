import Egg.Core.Blocks
import Egg.Core.Encode.Basic
import Lean
open Lean

namespace Egg

abbrev Block.Encoded := Expression

abbrev Blocks.Encoded := Array Block.Encoded

def Blocks.encode (blocks : Blocks) (cfg : Config.Encoding) : MetaM Blocks.Encoded :=
  blocks.mapM fun block => Egg.encode block cfg
