import Egg.Core.Config
import Lean
open Lean

namespace Egg

declare_syntax_cat _egg_opt
syntax ident (" : " term:max)? (str)? : _egg_opt

private def parseOpt : TSyntax `_egg_opt → MacroM (Ident × Term × String)
  | `(_egg_opt| $name:ident $[: $ty]? $[$descr]?) => do
    let ty := ty.getD <| ← `(Bool)
    let descr := descr.map (·.getString) |>.getD ""
    return (name, ty, descr)
  | _ => unreachable!

local macro "register_egg_options" opts:_egg_opt* : command => do
  let mut regs := #[]
  let mut names := #[]
  let mut defs := #[]
  for opt in opts do
    let (name, ty, descr) ← parseOpt opt
    let regName  := mkIdentFrom name (`egg ++ name.getId)
    regs := regs.push <| ← `(
      register_option $regName : $ty := {
        defValue := ({} : Config).$name
        descr := $(quote descr)
      }
    )
    names := names.push name
    defs := defs.push <| mkIdentFrom name (`egg ++ name.getId ++ `get)
  let cfgFromOpts ← `(
    def $(mkIdent `Config.fromOptions) : MetaM Config := return {
      $[$names:ident := $defs (← getOptions)]*
      toDebug := {}
    }
  )
  let cmds := regs.push cfgFromOpts
  return ⟨mkNullNode cmds⟩

register_egg_options
  slotted
  shapes
  betaReduceRws
  etaReduceRws
  natReduceRws
  builtins
  genStructProjRws
  genGoalTypeSpec
  genTcProjRws
  natLit
  eta
  etaExpand
  beta
  levels
  explosion
  derivedGuides
  genGroundEqs
  blockInvalidMatches
  shiftCapturedBVars "Note: Setting this to `true` also enables `egg.blockInvalidMatches`."
  unionSemantics
  conditionSubgoals
  optimizeExpl
  timeLimit : Nat "The number of seconds allotted to equality saturation before it aborts. Note
                   that the total invocation time of `egg` can exceed this time limit as it only
                   applies to the equality saturation step, and not other steps like equation
                   generation and proof reconstruction."
  nodeLimit : Nat
  iterLimit : Nat
  reporting
  flattenReports
  retryWithShapes "When proof reconstruction fails, try running again with `egg.shapes := true`."
  explLengthLimit : Nat
