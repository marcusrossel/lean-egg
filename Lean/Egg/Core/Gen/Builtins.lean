import Egg.Core.Rewrite.Basic
import Lean

open Lean Meta

namespace Egg.Rewrites

theorem imp_mp {p q : Prop} (imp : p → q) (h : p) : q :=
  imp h

-- TODO: `Nat.succ_eq_add_one` causes nat-lit rewrites to always be active.
--
-- We exclude `imp_mp` when subgoals are enabled, as this theorem proves everything in that case.
private def builtinTheorems (subgoals : Bool) : Array Name := Id.run do
  let mut thms := #[``Nat.succ_eq_add_one, ``ge_iff_le, ``gt_iff_lt]
  unless subgoals do thms := thms.push ``imp_mp
  return thms

def builtins (cfg : Config.Normalization) (subgoals : Bool) : MetaM Rewrites := do
  let mut rws := #[]
  let env ← getEnv
  let thms := builtinTheorems subgoals
  for thm in thms, idx in [:thms.size] do
    let info := env.find? thm |>.get!
    let lvlMVars ← List.replicateM info.numLevelParams mkFreshLevelMVar
    let val := info.instantiateValueLevelParams! lvlMVars
    let type := info.instantiateTypeLevelParams lvlMVars
    let some rs ← Rewrites.from? val type (.builtin idx) cfg
      | throwError "egg failed to create rewrites for builtin '{thm}'"
    rws := rws ++ rs
  return rws

end Rewrites

def genBuiltins (cfg : Config) : MetaM Rewrites := do
  Rewrites.builtins cfg cfg.subgoals
