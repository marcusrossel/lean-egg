import Egg.Core.Rewrite.Basic
import Egg.Core.MVars.Subst
import Lean
open Lean Meta

namespace Egg

private def Congr.nested? (cgr : Congr) : MetaM <| Option (Congr × Congr) := do
  let some lhs ← Congr.from? cgr.lhs | return none
  let some rhs ← Congr.from? cgr.rhs | return none
  return (lhs, rhs)

private def Congr.fresh (cgr : Congr) (mvars : MVars) (init : MVars.Subst := {}) :
    MetaM (Congr × MVars.Subst) := do
  let (_, subst) ← mvars.fresh (init := init)
  let cgr := { cgr with lhs := subst.apply cgr.lhs, rhs := subst.apply cgr.rhs }
  return (cgr, subst)

private structure Split where
  lhs     : Congr
  rhs     : Congr
  srcDir  : Direction
  rwSrc   : Source
  rwProof : Expr
  rwRel   : Congr.Rel

private def Split.type (split : Split) : MetaM Expr :=
  return .forallE .anonymous (← split.lhs.expr) (← split.rhs.expr) .default

private def Split.proof (split : Split) : MetaM Expr :=
  split.rwRel.mkMP split.rwProof

private def Split.src (split : Split) : Source :=
  .nestedSplit split.rwSrc split.srcDir

private def Split.genRewrites (split : Split) (cfg : Config.Normalization) : MetaM Rewrites := do
  let some rws ← Rewrites.from? (← split.proof) (← split.type) split.src cfg (normalize := false)
    | throwError "egg: internal error: 'Egg.Split.genRewrites failed to construct rewrite"
  return rws

private def genSplitsForRw (rw : Rewrite) (cfg : Config.Normalization) : MetaM Rewrites := do
  let some (lhs, rhs) ← rw.nested? | return #[]
  let mvars := rw.mvars.lhs.merge rw.mvars.rhs
  let (lhs, subst) ← lhs.fresh mvars
  let (rhs, _) ← rhs.fresh mvars (init := subst)
  Split.genRewrites { lhs, rhs, srcDir := rw.dir, rwSrc := rw.src, rwProof := rw.proof, rwRel := rw.rel } cfg

def genNestedSplits (targets : Rewrites) (cfg : Config.Normalization) : MetaM Rewrites := do
  targets.foldlM (init := #[]) fun acc rw => return acc ++ (← genSplitsForRw rw cfg)
