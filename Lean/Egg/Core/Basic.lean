import Egg.Core.Encode.Basic
import Egg.Core.Config
import Egg.Tactic.Rewrites
open Lean

namespace Egg
open Rewrite (Directions)

@[extern "lean_egg_explain_congr"]
private opaque explainCongrC
  (lhs rhs : Expression) (rwNames : Array String) (lhss rhss : Array Egg.Expression)
  (dirs : Array Directions) (optimizeExpl : Bool) (genNatLitRws : Bool) : String

-- Note: We wrap this in an `IndexT` so that we can trace the type indices later.
def explainCongr (cgr : Congr) (rws : Rewrites) (dirs : Array Directions) (cfg : Config) :
    IndexT MetaM String := do
  let names := rws.map (·.src.description)
  let lhs    ← encode cgr.lhs .goal cfg
  let rhs    ← encode cgr.rhs .goal cfg
  let lhss   ← rws.mapM fun rw => encode rw.lhs rw.src cfg
  let rhss   ← rws.mapM fun rw => encode rw.rhs rw.src cfg
  if cfg.exitPoint == .beforeEqSat
  then return ""
  else return explainCongrC lhs rhs names lhss rhss dirs cfg.optimizeExpl cfg.genNatLitRws
