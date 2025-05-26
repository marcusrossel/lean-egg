import Egg.Core.Encode.Basic
import Egg.Core.Rewrite.Basic
import Lean
open Lean

namespace Egg.Rewrite

def name (rw : Rewrite) : String :=
  match rw.dir with
  | .forward  => rw.src.description
  | .backward => s!"{rw.src.description}-rev"

-- IMPORTANT: The C interface to egg depends on the order of these fields.
structure Encoded where
  name  : String
  lhs   : Expression
  rhs   : Expression
  dirs  : Directions
  conds : Array Expression

def Condition.encode? (c : Rewrite.Condition) (cfg : Config.Encoding) :
    MetaM (Option Expression) := do
  if c.isProven then return none
  let type ← encode c.type cfg
  match c.kind with
  | .proof  => return s!"(proof {type})"
  | .tcInst => return s!"(inst {type})"

def encode (rw : Rewrite) (cfg : Config.Encoding) : MetaM Encoded :=
  return {
    name  := rw.name
    lhs   := ← Egg.encode rw.lhs cfg
    rhs   := ← Egg.encode rw.rhs cfg
    dirs  := .forward -- TODO: Remove this field
    conds := ← rw.conds.filterMapM (Condition.encode? · cfg)
  }

end Rewrite

namespace Rewrites

abbrev Encoded := Array Rewrite.Encoded

def encode (rws : Rewrites) (cfg : Config.Encoding) (subgoals : Bool) : MetaM Rewrites.Encoded :=
  rws.filterMapM fun rw => do if ← rw.isValid subgoals then rw.encode cfg else return none
