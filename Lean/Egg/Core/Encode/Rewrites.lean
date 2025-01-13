import Egg.Core.Encode.Basic
import Egg.Core.Premise.Rewrites
import Lean
open Lean

namespace Egg.Rewrite

-- IMPORTANT: The C interface to egg depends on the order of these fields.
structure Encoded where
  name  : String
  lhs   : Expression
  rhs   : Expression
  dirs  : Directions
  conds : Array Expression

def Condition.encode? (c : Rewrite.Condition) (ctx : EncodingCtx) : MetaM (Option Expression) := do
  if c.isProven then return none
  let type ← encode c.type ctx
  match c.kind with
  | .proof  => return s!"(proof {type})"
  | .tcInst => return s!"(inst {type})"

def encode (rw : Rewrite) (ctx : EncodingCtx) : MetaM Encoded :=
  return {
    name  := rw.src.description
    lhs   := ← Egg.encode rw.lhs ctx
    rhs   := ← Egg.encode rw.rhs ctx
    dirs  := rw.validDirs ctx.cfg.toErasure
    conds := ← rw.conds.filterMapM (Condition.encode? · ctx)
  }

end Rewrite

namespace Rewrites

abbrev Encoded := Array Rewrite.Encoded

def encode (rws : Rewrites) (ctx : EncodingCtx) : MetaM Rewrites.Encoded :=
  rws.mapM (·.encode ctx)
