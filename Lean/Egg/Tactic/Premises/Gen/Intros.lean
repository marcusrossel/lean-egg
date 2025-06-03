import Egg.Tactic.Premises.Gen.GenM
import Lean

open Lean Meta Elab Tactic

namespace Egg

def genIntros (fvars : Array FVarId) (cfg : Config) : TacticM Rewrites := do
  let mut rws := #[]
  for fvar in fvars, idx in [:fvars.size] do
    let proof := .fvar fvar
    let type   ← fvar.getType
    let src   := .intro idx
    rws := rws ++ (← Rewrites.from? proof type src cfg).getD #[]
    if cfg.groundEqs then
      if let some eq ← Rewrite.mkGroundEq? proof type (.ground src) cfg then
        rws := rws.push eq
  return rws
