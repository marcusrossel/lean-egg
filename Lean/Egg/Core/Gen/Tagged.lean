import Egg.Tactic.Rewrite.Rules.Parse
import Egg.Tactic.Baskets
import Lean
open Lean Elab Tactic

namespace Egg

def genTagged (cfg : Config) : TacticM Rewrite.Rules := do
  let mut prems := #[]
  for basket in cfg.baskets do
    prems := prems ++ (← extension.getAllBasketPremises basket)
  Rewrite.Rules.elabTagged prems cfg
