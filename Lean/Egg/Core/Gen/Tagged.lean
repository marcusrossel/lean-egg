import Egg.Tactic.Premises.Parse
import Egg.Tactic.Tags
import Lean
open Lean Elab Tactic

namespace Egg

def genTagged (cfg : Config) : TacticM Rewrites := do
  let mut prems := #[]
  for basket in cfg.baskets do
    prems := prems ++ (← extension.getBasket basket)
  Premises.elabTagged prems cfg
