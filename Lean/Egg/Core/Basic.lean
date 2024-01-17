import Egg.Core.Encode.Basic
import Egg.Core.Config
import Egg.Tactic.Rewrites
open Lean

namespace Egg
open Rewrite (Directions)

@[extern "lean_egg_check_eq"]
private opaque tryExplainEqC
  (lhs rhs : Expression) (rwNames : Array String) (lhss rhss : Array Egg.Expression)
  (dirs : Array Directions) (optimizeExpl : Bool) : String

-- Note: We wrap this in an `IndexT` so that we can trace the type indices later.
def tryExplainEq (lhs rhs : Expr) (rws : Rewrites) (dirs : Array Directions) (cfg : Config) :
    IndexT MetaM String := do
  let names := rws.map (·.src.description)
  let lhs    ← lhs.toEgg! .goal cfg
  let rhs    ← rhs.toEgg! .goal cfg
  let lhss   ← rws.mapM (·.lhs.toEgg! .rw cfg)
  let rhss   ← rws.mapM (·.rhs.toEgg! .rw cfg)
  if cfg.dbgBypass
  then return ""
  else return tryExplainEqC lhs rhs names lhss rhss dirs cfg.optimizeExpl
