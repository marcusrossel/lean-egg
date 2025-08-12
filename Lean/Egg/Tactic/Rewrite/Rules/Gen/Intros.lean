import Egg.Tactic.Rewrite.Rules.Gen.GenM

open Lean Meta Elab Tactic

namespace Egg

def genIntros (fvars : Array FVarId) (cfg : Config) : TacticM Rewrite.Rules := do
  let mut rules := ∅
  for fvar in fvars, idx in [:fvars.size] do
    let proof := .fvar fvar
    let type   ← fvar.getType
    let src   := .intro idx
    if let some rules' ← rules.add? src proof type cfg then
      rules := rules'
    if cfg.groundEqs then
      if let some rules' ← rules.add? (.ground src) proof type cfg .ground then
        rules := rules'
  return rules
