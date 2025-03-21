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
    withTraceNode cls (fun _ => return m!"Pruned ({pruned.size})") do pruned.trace #[] cls
    return all
where
  core : GenM Unit := open GenM in do
    generate  .intros     do genIntros goal.intros.unzip.fst cfg
    generate' .basic      do Premises.elab cfg cfg.genGroundEqs ps
    generate  .tagged     do genTagged cfg
    generate  .builtins   do genBuiltins cfg
    generate  .derived    do genDerived goal.toCongr (← allExceptGeneratedGroundEqs) guides cfg
    generate  .structProj do genStructProjRws goal.toCongr (← all) guides cfg
