import Egg.Core.Encode.Basic
import Egg.Core.Rewrites
import Egg.Core.Config

open Lean

namespace Egg

@[extern "lean_egg_check_eq"]
private opaque tryExplainEqC
  (lhs rhs : Expression) (rwNames : Array String) (lhsRws rhsRws : Array Expression)
  (rwDirs : Array Dir) : String

-- Note: We wrap this in a `TypeIndexT` so that we can trace the type indices later.
def tryExplainEq (lhs rhs : Lean.Expr) (rws : Array Rewrite) (cfg : Config) :
    TypeIndexT MetaM String := do
  let rwNames := rws.map (·.src.description)
  let rwDirs  := rws.map (·.dir)
  let lhs      ← lhs.toEgg! .goal cfg
  let rhs      ← rhs.toEgg! .goal cfg
  let lhsRws   ← rws.mapM (·.lhs.toEgg! .rw cfg)
  let rhsRws   ← rws.mapM (·.rhs.toEgg! .rw cfg)
  if cfg.dbgBypass
  then return ""
  else return tryExplainEqC lhs rhs rwNames lhsRws rhsRws rwDirs
