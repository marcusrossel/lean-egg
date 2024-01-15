import Egg.Core.Config
import Lean

open Lean Elab

namespace Egg

syntax egg_cfg := (Parser.Tactic.config)?

-- This is basically copy-pasted from `declare_config_elab`. The reason we don't use it directly is
-- because we'd have to figure out how to obtain the optional syntax to pass into the elaborator.
-- Cf. https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/elaborate.20context.20in.20attributes/near/303917935
section Elab

private unsafe def evalUnsafe (e : Expr) : TermElabM Config :=
    Meta.evalExpr' (safety := .unsafe) Config ``Config e

@[implemented_by evalUnsafe]
private opaque eval (e : Expr) : TermElabM Config

private def elabConfig (config : Term) : TermElabM Config := do
  eval (← withoutModifyingStateWithInfoAndMessages <| Meta.withLCtx {} {} <| withSaveInfoContext <|
    Term.withSynthesize do
      let c ← Term.elabTermEnsuringType config (Lean.mkConst ``Config)
      Term.synthesizeSyntheticMVarsNoPostponing
      instantiateMVars c)

section Elab

def Config.parse : TSyntax ``egg_cfg → TermElabM Config
  | `(egg_cfg|)                 => return {}
  | `(egg_cfg|(config := $cfg)) => elabConfig cfg
  | _                           => throwUnsupportedSyntax
