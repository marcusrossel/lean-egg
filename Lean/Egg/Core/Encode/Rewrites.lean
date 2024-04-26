import Egg.Core.Encode.Basic
import Egg.Core.Premise.Rewrites
import Lean
open Lean

namespace Egg

-- IMPORTANT: The C interface to egg depends on the order of these fields.
structure Rewrite.Encoded where
  name  : String
  lhs   : Expression
  rhs   : Expression
  dirs  : Directions
  conds : Array Expression

def Rewrite.encode (rw : Rewrite) (cfg : Config.Encoding) (amb : MVars.Ambient) : MetaM Encoded :=
  return {
    name  := rw.src.description
    lhs   := ← Egg.encode rw.lhs rw.src cfg amb
    rhs   := ← Egg.encode rw.rhs rw.src cfg amb
    dirs  := rw.validDirs
    conds := ← rw.conds.mapM fun cond => do Egg.encode cond.type rw.src cfg amb
  }

namespace Rewrites

abbrev Encoded := Array Rewrite.Encoded

def encode (rws : Rewrites) (cfg : Config.Encoding) (amb : MVars.Ambient) : MetaM Rewrites.Encoded :=
  rws.mapM (·.encode cfg amb)
