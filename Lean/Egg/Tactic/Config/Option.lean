import Egg.Core.Config
import Lean
open Lean

namespace Egg

declare_syntax_cat _egg_opt
syntax ident (" : " term:max)? : _egg_opt

private def parseOpt : TSyntax `_egg_opt → MacroM (Ident × Term)
  | `(_egg_opt| $name:ident $[: $ty]?) => return (name, ty.getD <| ← `(Bool))
  | _                                  => unreachable!

local macro "register_egg_options" opts:_egg_opt* : command => do
  let mut regs := #[]
  let mut names := #[]
  let mut defs := #[]
  for opt in opts do
    let (name, ty) ← parseOpt opt
    let regName  := mkIdentFrom name (`egg ++ name.getId)
    regs := regs.push <| ← `(register_option $regName : $ty := { defValue := ({} : Config).$name})
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
  eraseProofs
  shapes
  betaReduceRws
  etaReduceRws
  natReduceRws
  builtins
  genTcProjRws
  genTcSpecRws
  genGoalTcSpec
  genNatLitRws
  genEtaRw
  genBetaRw
  genLevelRws
  explosion
  blockInvalidMatches
  shiftCapturedBVars
  conditionSubgoals
  optimizeExpl
  timeLimit : Nat
  nodeLimit : Nat
  iterLimit : Nat
  reporting
  flattenReports
