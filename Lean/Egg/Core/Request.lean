import Egg.Core.Encode.Basic
import Egg.Core.Config
import Egg.Core.Explanation.Basic
import Egg.Tactic.Rewrites
open Lean

namespace Egg

@[extern "lean_egg_explain_congr"]
private opaque explainCongr
  (lhs rhs : Expression) (rwNames : Array String) (lhss rhss : Array Egg.Expression)
  (dirs : Array Directions) (optimizeExpl : Bool) (genNatLitRws : Bool) : String

protected structure Request.Rewrites where
  private mk ::
  names : Array String
  lhss  : Array Expression
  rhss  : Array Expression
  dirs  : Array Rewrite.Directions

structure Request where
  private mk ::
  lhs : Expression
  rhs : Expression
  rws : Request.Rewrites
  optimizeExpl : Bool
  genNatLitRws : Bool

namespace Request

def encoding (goal : Congr) (rws : Rewrites) (dirs : Array Rewrite.Directions) (cfg : Config) :
    MetaM Request :=
  return {
    lhs          := ← encode goal.lhs .goal cfg
    rhs          := ← encode goal.rhs .goal cfg
    rws.names    := rws.map (·.src.description)
    rws.lhss     := ← rws.mapM fun rw => encode rw.lhs rw.src cfg
    rws.rhss     := ← rws.mapM fun rw => encode rw.rhs rw.src cfg
    rws.dirs     := dirs
    optimizeExpl := cfg.optimizeExpl
    genNatLitRws := cfg.genNatLitRws
  }

def run (r : Request) : Explanation.Raw :=
  explainCongr r.lhs r.rhs r.rws.names r.rws.lhss r.rws.rhss r.rws.dirs r.optimizeExpl r.genNatLitRws
