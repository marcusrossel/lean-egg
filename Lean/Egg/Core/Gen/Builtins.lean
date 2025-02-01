import Egg.Core.Premise.Rewrites
import Lean

open Lean Meta

namespace Egg.Rewrites

theorem imp_mp {p q : Prop} (imp : p → q) (h : p) : q :=
  imp h

private def builtinTheorems := #[
  -- TODO: Add this once you figure out how to handle unbound condition mvars: ``imp_mp,
  ``Nat.succ_eq_add_one,
  ``ge_iff_le,
  ``gt_iff_lt
]

def builtins (cfg : Config.Normalization) : MetaM Rewrites := do
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

end Rewrites

def genBuiltins (cfg : Config) : MetaM Rewrites := do
  if cfg.builtins then Rewrites.builtins cfg else return #[]
