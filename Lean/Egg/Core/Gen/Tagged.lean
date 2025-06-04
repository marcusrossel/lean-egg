import Egg.Tactic.Premises.Parse
import Egg.Tactic.Baskets
import Lean
open Lean Elab Tactic

namespace Egg

def genTagged (cfg : Config) : TacticM Rewrites := do
  let mut prems := #[]
  for basket in cfg.baskets do
    prems := prems ++ (← extension.getAllBasketPremises basket)
  Premises.elabTagged prems cfg
