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

def Rewrite.encode (rw : Rewrite) (ctx : EncodingCtx) : MetaM Encoded :=
  return {
    name  := rw.src.description
    lhs   := ← Egg.encode rw.lhs ctx
    rhs   := ← Egg.encode rw.rhs ctx
    dirs  := rw.validDirs
    conds := ← rw.conds.mapM fun cond => do Egg.encode cond.type ctx
  }

namespace Rewrites

abbrev Encoded := Array Rewrite.Encoded

def encode (rws : Rewrites) (ctx : EncodingCtx) : MetaM Rewrites.Encoded :=
  rws.mapM (·.encode ctx)
