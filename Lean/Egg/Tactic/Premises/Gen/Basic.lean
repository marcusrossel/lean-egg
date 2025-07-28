import Egg.Core.Gen.Builtins
import Egg.Core.Gen.Tagged
import Egg.Core.Gen.StructProjs
import Egg.Tactic.Goal
import Egg.Tactic.Baskets
import Egg.Tactic.Premises.Parse
import Egg.Tactic.Premises.Gen.GenM
import Egg.Tactic.Premises.Gen.Intros
import Egg.Tactic.Premises.Gen.Derived
import Egg.Tactic.Trace
import Lean

open Lean Meta Elab Tactic

namespace Egg.Premises

def gen (goal : Goal) (ps : TSyntax `egg_premises) (guides : Guides) (cfg : Config) :
    TacticM Rewrites := do
  withTraceNode `egg.rewrites (fun _ => return "Rewrites") do
    let { all, pruned } ← GenM.run core
    withTraceNode `egg.rewrites.pruned (fun _ => return m!"Pruned ({pruned.rws.size})") do
      pruned.rws.tracePruned pruned.reasons `egg.rewrites.pruned cfg.subgoals
    return all
where
  genBasic : GenM Premises := do
    let basic ← Premises.elab cfg cfg.groundEqs ps
    for stx in basic.rws.stxs do
      let `($name:ident) := stx | continue
      for basket in cfg.baskets do
        if ← extension.basketContains basket name.getId then
          logWarningAt name m!"This theorem already appears in the egg basket '{basket}'"
    return basic
  core : GenM Unit := open GenM in do
    generate  .intros     cfg.subgoals do genIntros goal.intros.unzip.fst cfg
    generate' .basic      cfg.subgoals do genBasic
    generate  .tagged     cfg.subgoals do genTagged cfg
    generate  .builtins   cfg.subgoals do genBuiltins cfg
    generate  .derived    cfg.subgoals do genDerived goal.toCongr (← allExceptGeneratedGroundEqs) guides cfg
    generate  .structProj cfg.subgoals do genStructProjRws goal.toCongr (← all) guides cfg
