import Egg.Core.Premise.Rewrites
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
  rwSrc   : Source
  dir     : Direction
  rwProof : Expr
  rwRel   : Congr.Rel

private def Split.type (split : Split) : MetaM Expr :=
  match split.dir with
  | .forward  => return .forallE .anonymous (← split.lhs.expr) (← split.rhs.expr) .default
  | .backward => return .forallE .anonymous (← split.rhs.expr) (← split.lhs.expr) .default

private def Split.proof (split : Split) : MetaM Expr :=
  match split.dir with
  | .forward  => split.rwRel.mkMP  split.rwProof
  | .backward => split.rwRel.mkMPR split.rwProof

private def Split.src (split : Split) : Source :=
  .nestedSplit split.rwSrc split.dir

private def Split.genRewrite (split : Split) (cfg : Rewrite.Config) : MetaM Rewrite := do
  let some rw ← Rewrite.from? (← split.proof) (← split.type) split.src cfg (normalize := false)
    | throwError "egg: internal error: 'Egg.genSingleSplit' failed to construct rewrite"
  return rw

private def genSplitsForRw (rw : Rewrite) (cfg : Rewrite.Config) : MetaM Rewrites := do
  let some (lhs, rhs) ← rw.nested? | return #[]
  let mvars := rw.mvars.lhs.merge rw.mvars.rhs
  let (lhs, subst) ← lhs.fresh mvars
  let (rhs, _) ← rhs.fresh mvars (init := subst)
  #[Direction.forward, .backward].mapM fun dir => do
    Split.genRewrite { lhs, rhs, rwSrc := rw.src, dir, rwProof := rw.proof, rwRel := rw.rel } cfg

def genNestedSplits (targets : Rewrites) (cfg : Rewrite.Config) : MetaM Rewrites := do
  targets.foldlM (init := #[]) fun acc rw => return acc ++ (← genSplitsForRw rw cfg)
