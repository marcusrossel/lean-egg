import Egg.Core.Encode.Basic
import Egg.Core.Rewrites
import Lean
open Lean

namespace Egg

-- IMPORTANT: The C interface to egg depends on the order of these fields.
structure Rewrite.Encoded where
  name : String
  lhs  : Expression
  rhs  : Expression
  dirs : Directions

def Rewrite.encode (cfg : Config.Encoding) (rw : Rewrite) : MetaM Encoded :=
  return {
    name := rw.src.description
    lhs  := ← Egg.encode rw.lhs rw.src cfg
    rhs  := ← Egg.encode rw.rhs rw.src cfg
    dirs := rw.validDirs
  }

namespace Rewrites

abbrev Encoded := Array Rewrite.Encoded

def encode (rws : Rewrites) (cfg : Config.Encoding) : MetaM Rewrites.Encoded :=
  rws.mapM (Rewrite.encode cfg)
