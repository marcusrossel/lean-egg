import Egg.Core.Gen.Builtins
import Egg.Core.Gen.Tagged
import Egg.Core.Gen.GoalTypeSpecialization
import Egg.Core.Gen.Explosion
import Egg.Core.Gen.TcProjs
import Egg.Core.Gen.StructProjs
import Egg.Tactic.Goal
import Egg.Tactic.Baskets
import Egg.Tactic.Rewrite.Rules.Parse
import Egg.Tactic.Rewrite.Rules.Gen.GenM
import Egg.Tactic.Rewrite.Rules.Gen.Intros
import Egg.Tactic.Trace

open Lean Meta Elab Tactic

namespace Egg.Rewrite.Rules

def gen (goal : Goal) (args : TSyntax `egg_args) (guides : Guides) (cfg : Config) : TacticM Rules := do
  withTraceNode `egg.rewrites (fun _ => return "Rewrites") do
    let { all, pruned } ← GenM.run core
    withTraceNode `egg.rewrites.pruned (fun _ => return m!"Pruned ({pruned.rules.rws.size})") do
      pruned.rules.tracePruned pruned.reasons `egg.rewrites.pruned cfg.subgoals
    return all
where
  genBasic : GenM Rules := do
    let basic ← Rules.elab cfg cfg.groundEqs args
    for (_, stx) in basic.stxs do
      let `($name:ident) := stx | continue
      for basket in cfg.baskets do
        if ← extension.basketContains basket name.getId then
          logWarningAt name m!"This theorem already appears in the egg basket '{basket}'"
    return basic
  genTcProjs : GenM Rules := open GenM in do
    let rws ← allExceptGeneratedGroundEqs
    let targets := rws.tcProjTargets ++ goal.tcProjTargets .goal ++ guides.tcProjTargets
    genTcProjReductions targets cfg
  core : GenM Unit := open GenM in do
    generate .intros       cfg do genIntros goal.intros.unzip.fst cfg
    generate .basic        cfg do genBasic
    generate .tagged       cfg do genTagged cfg
    generate .builtins     cfg do genBuiltins cfg
    -- Note: the order of the following derived rewrites is chosen explicitly.
    generate .goalTypeSpec cfg do genGoalTypeSpecializations (← allExceptGeneratedGroundEqs) goal.toCongr cfg.subgoals
    generate .explosion    cfg do genExplosions (← allExceptGeneratedGroundEqs) cfg.subgoals
    generate .tcProj       cfg do genTcProjs
    generate .structProj   cfg do genStructProjRws goal.toCongr (← all) guides cfg
