import Egg.Core.Encode.Basic
import Egg.Core.Rewrite.Basic
import Lean
open Lean

namespace Egg.Rewrite

-- IMPORTANT: The C interface to egg depends on the order of these fields.
structure Encoded where
  name  : String
  lhs   : Expression
  rhs   : Expression
  conds : Array Expression

nonrec def Condition.encode (c : Rewrite.Condition) (cfg : Config.Encoding) : MetaM Expression := do
  let type ← encode c.type cfg
  match c.kind with
  | .proof  => return s!"(proof {type})"
  | .tcInst => return s!"(inst {type})"

def encode (rw : Rewrite) (cfg : Config.Encoding) : MetaM Encoded :=
  return {
    name  := s!"{rw.dir.description}{rw.src.description}"
    lhs   := ← Egg.encode rw.lhs cfg
    rhs   := ← Egg.encode rw.rhs cfg
    conds := ← rw.conds.active.mapM (Condition.encode · cfg)
  }

end Rewrite

namespace Rewrites

abbrev Encoded := Array Rewrite.Encoded

def encode (rws : Rewrites) (cfg : Config.Encoding) (subgoals : Bool) : MetaM Rewrites.Encoded :=
  rws.filterMapM fun rw => do if ← rw.isValid subgoals then rw.encode cfg else return none
