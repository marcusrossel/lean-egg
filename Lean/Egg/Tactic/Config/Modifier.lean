import Egg.Tactic.Config.Option
import Lean

open Lean Elab

namespace Egg.Config

structure Modifier where
  slotted         : Option Bool            := none
  shapes          : Option Bool            := none
  betaReduceRws   : Option Bool            := none
  etaReduceRws    : Option Bool            := none
  natReduceRws    : Option Bool            := none
  builtins        : Option Bool            := none
  structProjs     : Option Bool            := none
  goalTypeSpec    : Option Bool            := none
  tcProjs         : Option Bool            := none
  natLit          : Option Bool            := none
  eta             : Option Bool            := none
  etaExpand       : Option Bool            := none
  beta            : Option Bool            := none
  levels          : Option Bool            := none
  explosion       : Option Bool            := none
  derivedGuides   : Option Bool            := none
  groundEqs       : Option Bool            := none
  unionSemantics  : Option Bool            := none
  subgoals        : Option Bool            := none
  optimizeExpl    : Option Bool            := none
  timeLimit       : Option Nat             := none
  nodeLimit       : Option Nat             := none
  iterLimit       : Option Nat             := none
  reporting       : Option Bool            := none
  flattenReports  : Option Bool            := none
  retryWithShapes : Option Bool            := none
  explLengthLimit : Option Nat             := none
  exitPoint       : Option Debug.ExitPoint := none
  proofFuel?      : Option Nat             := none
  vizPath         : Option String          := none

def modify (cfg : Config) (mod : Modifier) : Config where
  shapes          := mod.shapes.getD cfg.shapes
  betaReduceRws   := mod.betaReduceRws.getD cfg.betaReduceRws
  etaReduceRws    := mod.etaReduceRws.getD cfg.etaReduceRws
  natReduceRws    := mod.natReduceRws.getD cfg.natReduceRws
  builtins        := mod.builtins.getD cfg.builtins
  structProjs     := mod.structProjs.getD cfg.structProjs
  goalTypeSpec    := mod.goalTypeSpec.getD cfg.goalTypeSpec
  tcProjs         := mod.tcProjs.getD cfg.tcProjs
  natLit          := mod.natLit.getD cfg.natLit
  eta             := mod.eta.getD cfg.eta
  etaExpand       := mod.etaExpand.getD cfg.etaExpand
  beta            := mod.beta.getD cfg.beta
  levels          := mod.levels.getD cfg.levels
  explosion       := mod.explosion.getD cfg.explosion
  derivedGuides   := mod.derivedGuides.getD cfg.derivedGuides
  groundEqs       := mod.groundEqs.getD cfg.groundEqs
  unionSemantics  := mod.unionSemantics.getD cfg.unionSemantics
  subgoals        := mod.subgoals.getD cfg.subgoals
  optimizeExpl    := mod.optimizeExpl.getD cfg.optimizeExpl
  timeLimit       := mod.timeLimit.getD cfg.timeLimit
  nodeLimit       := mod.nodeLimit.getD cfg.nodeLimit
  iterLimit       := mod.iterLimit.getD cfg.iterLimit
  reporting       := mod.reporting.getD cfg.reporting
  flattenReports  := mod.flattenReports.getD cfg.flattenReports
  retryWithShapes := mod.retryWithShapes.getD cfg.retryWithShapes
  explLengthLimit := mod.explLengthLimit.getD cfg.explLengthLimit
  proofFuel?      := match mod.proofFuel? with | some p => p | none => cfg.proofFuel?
  exitPoint       := mod.exitPoint.getD cfg.exitPoint
  vizPath         := match mod.vizPath with | some p => p | none => cfg.vizPath

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
