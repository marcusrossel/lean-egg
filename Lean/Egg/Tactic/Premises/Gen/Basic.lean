import Egg.Core.Gen.Builtins
import Egg.Core.Gen.Tagged
import Egg.Core.Gen.StructProjs
import Egg.Tactic.Goal
import Egg.Tactic.Tags
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
    let cls := `egg.rewrites
    cfg.toDefEq.trace cls
    withTraceNode cls (fun _ => return m!"Pruned ({pruned.rws.size})") do
      pruned.rws.tracePruned pruned.reasons cls cfg.conditionSubgoals
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
    generate  .intros     cfg.conditionSubgoals do genIntros goal.intros.unzip.fst cfg
    generate' .basic      cfg.conditionSubgoals do genBasic
    generate  .tagged     cfg.conditionSubgoals do genTagged cfg
    generate  .builtins   cfg.conditionSubgoals do genBuiltins cfg
    generate  .derived    cfg.conditionSubgoals do genDerived goal.toCongr (← allExceptGeneratedGroundEqs) guides cfg
    generate  .structProj cfg.conditionSubgoals do genStructProjRws goal.toCongr (← all) guides cfg
