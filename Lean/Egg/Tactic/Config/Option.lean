import Egg.Core.Config
import Lean
open Lean

namespace Egg

local macro "register_egg_options" opts:ident* : command => do
  let regs ← opts.mapM fun (opt : Ident) => do
    let name := mkIdentFrom opt (`egg ++ opt.getId)
    `(register_option $name : Bool := { defValue := ({} : Config).$opt})
  let defIdents := opts.map fun opt => mkIdentFrom opt (`egg ++ opt.getId ++ `get)
  let cfgFromOpts ← `(
    def $(mkIdent `Config.fromOptions) : MetaM Config := return {
      $[$opts:ident := $defIdents (← getOptions)]*
      toDebug := {}
    }
  )
  let cmds := regs.push cfgFromOpts
  return ⟨mkNullNode cmds⟩

register_egg_options
  eraseProofs
  eraseLambdaDomains
  eraseForallDomains
  betaReduceRws
  etaReduceRws
  natReduceRws
  genTcProjRws
  genTcSpecRws
  genNatLitRws
  genEtaRw
  genBetaRw
  blockInvalidMatches
  shiftCapturedBVars
  optimizeExpl
