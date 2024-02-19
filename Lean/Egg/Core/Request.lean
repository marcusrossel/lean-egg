import Egg.Core.Encode.Basic
import Egg.Core.Config
import Egg.Core.Explanation.Basic
import Egg.Core.Rewrites.Basic
open Lean

namespace Egg

@[extern "lean_egg_explain_congr"]
private opaque explainCongr
  (lhs rhs : Expression) (rwNames : Array String) (lhss rhss : Array Egg.Expression)
  (dirs : Array Directions) (optimizeExpl : Bool) (genNatLitRws : Bool) : String

protected structure Request.Rewrites where
  private mk ::
  names : Array String             := #[]
  lhss  : Array Expression         := #[]
  rhss  : Array Expression         := #[]
  dirs  : Array Rewrite.Directions := #[]

structure Request where
  private mk ::
  lhs : Expression
  rhs : Expression
  rws : Request.Rewrites
  optimizeExpl : Bool
  genNatLitRws : Bool

namespace Request

def Rewrites.encoding (rws : Rewrites) (cfg : Config.Encoding) : MetaM Request.Rewrites :=
  rws.foldlM (init := {}) fun acc rw => return {
    names := acc.names.push <| rw.src.description
    lhss  := acc.lhss.push  <| ← encode rw.lhs rw.src cfg
    rhss  := acc.rhss.push  <| ← encode rw.rhs rw.src cfg
    dirs  := acc.dirs.push  <| rw.validDirs
  }

def encoding (goal : Congr) (rws : Rewrites) (cfg : Config) : MetaM Request :=
  return {
    lhs          := ← encode goal.lhs .goal cfg.toEncoding
    rhs          := ← encode goal.rhs .goal cfg.toEncoding
    rws          := ← Rewrites.encoding rws cfg.toEncoding
    optimizeExpl := cfg.optimizeExpl
    genNatLitRws := cfg.genNatLitRws
  }

def run (r : Request) : Explanation.Raw :=
  explainCongr r.lhs r.rhs r.rws.names r.rws.lhss r.rws.rhss r.rws.dirs r.optimizeExpl r.genNatLitRws
