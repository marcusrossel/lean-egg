import Egg.Core.Encode.Rewrites
import Egg.Core.Config
import Egg.Core.Gen.Explosion
import Egg.Core.Explanation.Basic
import Egg.Core.Rewrites.Basic
open Lean

namespace Egg

-- TODO: Can you pass a `Rewrites.Encoded` instead of splitting it into arrays of its fields?
@[extern "lean_egg_explain_congr"]
private opaque explainCongr
  (lhs rhs : Expression) (rwNames : Array String) (lhss rhss : Array Expression)
  (dirs : Array Rewrite.Directions) (optimizeExpl : Bool) (genNatLitRws : Bool) : String

structure Request where
  private mk ::
  lhs : Expression
  rhs : Expression
  rws : Rewrites.Encoded
  optimizeExpl : Bool
  genNatLitRws : Bool

namespace Request

def encoding (goal : Congr) (rws : Rewrites) (cfg : Config) : MetaM Request := do
  return {
    lhs          := ← encode goal.lhs .goal cfg.toEncoding
    rhs          := ← encode goal.rhs .goal cfg.toEncoding
    rws          := ← rws.encode cfg.toEncoding
    optimizeExpl := cfg.optimizeExpl
    genNatLitRws := cfg.genNatLitRws
  }

def run (r : Request) : Explanation.Raw :=
  explainCongr r.lhs r.rhs r.rws.names r.rws.lhss r.rws.rhss r.rws.dirs r.optimizeExpl r.genNatLitRws
