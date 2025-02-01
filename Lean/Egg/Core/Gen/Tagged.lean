import Egg.Tactic.Premises.Parse
import Egg.Tactic.Tags
import Lean
open Lean Elab Tactic

namespace Egg

def genTagged (cfg : Config) : TacticM Rewrites := do
  let some _ := cfg.basket? | return #[]
  -- TODO: This should use the basket name to find the proper extension.
  let prems := extension.getState (← getEnv)
  Premises.elabTagged prems cfg
