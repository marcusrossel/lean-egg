import Egg.Core.Encode.Basic
import Egg.Core.Config
import Egg.Tactic.Rewrites
open Lean

namespace Egg
open Rewrite (Directions)

@[extern "lean_egg_check_eq"]
private opaque explainCongrC
  (lhs rhs : Expression) (rwNames : Array String) (lhss rhss : Array Egg.Expression)
  (dirs : Array Directions) (optimizeExpl : Bool) : String

-- TODO: Clean this up.

-- Note: We wrap this in an `IndexT` so that we can trace the type indices later.
def explainCongr (cgr : Congr) (rws : Rewrites) (dirs : Array Directions) (cfg : Config) :
    IndexT MetaM (String × Rewrites × Array Directions) := do
  let lhs     ← cgr.lhs.toEgg .goal cfg
  let rhs     ← cgr.rhs.toEgg .goal cfg
  let rwLhss  ← rws.mapM fun rw => rw.lhs.toEgg rw.src cfg
  let rwRhss  ← rws.mapM fun rw => rw.rhs.toEgg rw.src cfg
  let (tcProjs, tcDirs) := Array.unzip <| ← (← IndexT.getTcProjReductions).filterMapM fun rw => do
    let some dirs ← rw.validDirs cfg.eraseULvls | return none
    return some (rw, dirs)
  let names  := (rws ++ tcProjs).map (·.src.description)
  let dirs   := dirs ++ tcDirs
  let tcLhss  ← tcProjs.mapM fun rw => rw.lhs.toEgg rw.src { cfg with genTcProjRws := false }
  let tcRhss  ← tcProjs.mapM fun rw => rw.rhs.toEgg rw.src { cfg with genTcProjRws := false }
  let lhss   := rwLhss ++ tcLhss
  let rhss   := rwRhss ++ tcRhss
  let allRws := rws ++ tcProjs
  if cfg.exitPoint == .beforeEqSat
  then return ("", allRws, dirs)
  else return (explainCongrC lhs rhs names lhss rhss dirs cfg.optimizeExpl, allRws, dirs)
