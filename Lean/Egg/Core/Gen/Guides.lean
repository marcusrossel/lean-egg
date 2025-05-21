import Egg.Core.Rewrite.Basic
import Egg.Core.Guides
import Lean

open Lean Meta

namespace Egg

-- Note: Mvars which are not at the current mctx depth are considered closed.
private partial def closedSubexprs (expr : Expr) : MetaM ExprSet := do
  if expr.hasLooseBVars then
    closedChildSubexprs expr
  else if expr.hasMVar || expr.hasLevelMVar then
    let { result := mvars, .. } := expr.collectMVars {}
    unless ← mvars.allM fun m => return !(← m.isAssignable) do return (← closedChildSubexprs expr)
    let { result := lmvars, .. } := collectLevelMVars {} expr
    unless ← lmvars.allM fun m => return !(← isLevelMVarAssignable m) do return (← closedChildSubexprs expr)
    return {expr}
  else
    return {expr}
where
  closedChildSubexprs (expr : Expr) : MetaM ExprSet :=
    expr.foldlM (init := ∅) fun acc child =>
      return acc.union (← closedSubexprs child)

private def deriveGuides (rw : Rewrite) : MetaM ExprSet := do
  let mut result := ∅
  result := result.union (← closedSubexprs rw.lhs)
  result := result.union (← closedSubexprs rw.rhs)
  for cond in rw.conds do result := result.union (← closedSubexprs cond.type)
  return result

def genDerivedGuides (goal : Congr) (rws : Rewrites) : MetaM Guides := do
  let guides : ExprSet ← rws.foldlM (init := {← goal.expr}) (return ·.union <| ← deriveGuides ·)
  let mut result := #[]
  for guide in guides, idx in [:guides.size] do
    result := result.push <| ← Guide.from guide (.guide idx (derived := true))
  return result
