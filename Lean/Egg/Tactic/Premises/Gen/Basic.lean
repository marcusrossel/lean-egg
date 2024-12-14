import Egg.Core.Gen.Builtins
import Egg.Core.Gen.Tagged
import Egg.Tactic.Tags
import Egg.Tactic.Premises.Parse
import Egg.Tactic.Premises.Gen.GenM
import Egg.Tactic.Premises.Gen.Derived
import Egg.Tactic.Trace
import Lean

open Lean Meta Elab Tactic

namespace Egg.Premises

-- TODO: Remove the distinction between the different kinds of auto-generated rewrite categories.
--       Just have one `auto` category. Then see what follows from that.

def gen
    (goal : Congr) (ps : TSyntax `egg_premises) (guides : Guides) (cfg : Config)
    (amb : MVars.Ambient) : TacticM (Rewrites × Facts) := do
  withTraceNode `egg.rewrites (fun _ => return "Rewrites") do
    let { all, pruned, facts } ← GenM.run core
    let cls := `egg.rewrites
    cfg.toDefEq.trace cls
    withTraceNode cls (fun _ => return m!"Hypotheses ({facts.elems.size})") do facts.elems.trace facts.stxs cls
    withTraceNode cls (fun _ => return m!"Pruned ({pruned.size})") do pruned.trace #[] cls
    return (all, facts.elems)
where
  core : GenM Unit := open GenM in do
    generate' .basic    do Premises.elab { cfg with amb } ps
    generate  .tagged   do genTagged cfg amb
    generate  .builtins do genBuiltins cfg amb
    generate  .derived  do genDerived goal (← all) (← GenM.facts).elems guides cfg amb
