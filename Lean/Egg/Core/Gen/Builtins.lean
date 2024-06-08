import Egg.Core.Premise.Rewrites
import Lean

open Lean Meta

namespace Egg.Rewrites

private def builtinTheorems := #[
  ``Nat.succ_eq_add_one
  -- TODO: These cause a stack overflow in `Stack Overflow.lean`.
  -- ``ge_iff_le
  -- ``gt_iff_lt
]

def builtins (cfg : Rewrite.Config) : MetaM Rewrites := do
  let mut rws := #[]
  let env ← getEnv
  for thm in builtinTheorems, idx in [:builtinTheorems.size] do
    let info := env.find? thm |>.get!
    let lvlMVars ← List.replicateM info.numLevelParams mkFreshLevelMVar
    let val := info.instantiateValueLevelParams! lvlMVars
    let type := info.instantiateTypeLevelParams lvlMVars
    let rw? ← Rewrite.from? val type (.builtin idx) cfg
    rws := rws.push rw?.get!
  return rws
