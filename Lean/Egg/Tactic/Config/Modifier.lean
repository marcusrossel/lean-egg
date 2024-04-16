import Egg.Tactic.Config.Option
import Lean

open Lean Elab

namespace Egg.Config

structure Modifier where
  eraseProofs         : Option Bool            := none
  eraseLambdaDomains  : Option Bool            := none
  eraseForallDomains  : Option Bool            := none
  betaReduceRws       : Option Bool            := none
  etaReduceRws        : Option Bool            := none
  genTcProjRws        : Option Bool            := none
  genTcSpecRws        : Option Bool            := none
  genNatLitRws        : Option Bool            := none
  genEtaRw            : Option Bool            := none
  genBetaRw           : Option Bool            := none
  shiftCapturedBVars  : Option Bool            := none
  blockInvalidMatches : Option Bool            := none
  optimizeExpl        : Option Bool            := none
  traceSubstitutions  : Option Bool            := none
  traceBVarCorrection : Option Bool            := none
  exitPoint           : Option Debug.ExitPoint := none
  vizPath             : Option String          := none

def modify (cfg : Config) (mod : Modifier) : Config where
  eraseProofs         := mod.eraseProofs.getD cfg.eraseProofs
  eraseLambdaDomains  := mod.eraseLambdaDomains.getD cfg.eraseLambdaDomains
  eraseForallDomains  := mod.eraseForallDomains.getD cfg.eraseForallDomains
  betaReduceRws       := mod.betaReduceRws.getD cfg.betaReduceRws
  etaReduceRws        := mod.etaReduceRws.getD cfg.etaReduceRws
  genTcProjRws        := mod.genTcProjRws.getD cfg.genTcProjRws
  genTcSpecRws        := mod.genTcSpecRws.getD cfg.genTcSpecRws
  genNatLitRws        := mod.genNatLitRws.getD cfg.genNatLitRws
  genEtaRw            := mod.genEtaRw.getD cfg.genEtaRw
  genBetaRw           := mod.genBetaRw.getD cfg.genBetaRw
  shiftCapturedBVars  := mod.shiftCapturedBVars.getD cfg.shiftCapturedBVars
  blockInvalidMatches := mod.blockInvalidMatches.getD cfg.blockInvalidMatches
  optimizeExpl        := mod.optimizeExpl.getD cfg.optimizeExpl
  traceSubstitutions  := mod.traceSubstitutions.getD cfg.traceSubstitutions
  traceBVarCorrection := mod.traceBVarCorrection.getD cfg.traceBVarCorrection
  exitPoint           := mod.exitPoint.getD cfg.exitPoint
  vizPath             := match mod.vizPath with | some p => p | none => cfg.vizPath

namespace Modifier

syntax egg_cfg_mod := (Parser.Tactic.config)?

-- This is basically copy-pasted from `declare_config_elab`. The reason we don't use it directly is
-- because we'd have to figure out how to obtain the optional syntax to pass into the elaborator.
-- Cf. https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/elaborate.20context.20in.20attributes/near/303917935
section Elab

private unsafe def evalUnsafe (e : Expr) : TermElabM Modifier :=
  Meta.evalExpr' (safety := .unsafe) Modifier ``Modifier e

@[implemented_by evalUnsafe]
private opaque eval (e : Expr) : TermElabM Modifier

private def elabConfigModifier (config : Term) : TermElabM Modifier := do
  eval (← withoutModifyingStateWithInfoAndMessages <| Meta.withLCtx {} {} <| withSaveInfoContext <|
    Term.withSynthesize do
      let mod ← Term.elabTermEnsuringType config (Lean.mkConst ``Modifier)
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars mod)

end Elab

def parse : TSyntax ``egg_cfg_mod → TermElabM Modifier
  | `(egg_cfg_mod|)                 => return {}
  | `(egg_cfg_mod|(config := $mod)) => elabConfigModifier mod
  | _                               => throwUnsupportedSyntax
