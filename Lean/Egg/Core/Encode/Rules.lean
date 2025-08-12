import Egg.Core.Encode.Basic
import Egg.Core.Rewrite.Rule
import Lean
open Lean

namespace Egg.Rewrite

-- IMPORTANT: The C interface to egg depends on the order of these fields.
structure Rule.Encoded where
  name  : String
  lhs   : Expression
  rhs   : Expression
  conds : Array Expression

nonrec def Condition.encode (c : Rewrite.Condition) (cfg : Config.Encoding) : MetaM Expression := do
  let type ← encode c.type cfg
  match c.kind with
  | .proof  => return s!"(proof {type})"
  | .tcInst => return s!"(inst {type})"

nonrec def Rule.encode (rule : Rule) (cfg : Config.Encoding) : MetaM Rule.Encoded :=
  return {
    name  := rule.id.description
    lhs   := ← encode rule.rw.lhs cfg
    rhs   := ← encode rule.rw.rhs cfg
    conds := ← rule.rw.conds.active.mapM (·.encode cfg)
  }

abbrev Rules.Encoded := Array Rule.Encoded

def Rules.encode (rules : Rules) (cfg : Config.Encoding) (subgoals : Bool) : MetaM Rules.Encoded :=
  rules.entries.filterMapM fun rule => do
    if ← rule.rw.isValid subgoals then
      rule.encode cfg
    else
      return none
