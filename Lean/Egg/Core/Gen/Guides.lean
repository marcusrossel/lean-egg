import Egg.Core.Premise.Rewrites
import Egg.Core.Guides
import Lean

open Lean Meta

namespace Egg

private partial def subexprsWithoutMVars (expr : Expr) (amb : MVars.Ambient) : ExprSet := Id.run do
  if !expr.hasMVar && !expr.hasLooseBVars then return {expr}
  -- TODO: We need to consider level mvars here once collection of ambient level mvars is implemented.
  if !expr.hasLevelMVar && !expr.hasLooseBVars then
    let { result := mvars, .. } := expr.collectMVars {}
    if mvars.all (amb.expr.contains ·) then return {expr}
  expr.foldlM (init := ∅) fun acc child => acc.union (subexprsWithoutMVars child amb)

private def deriveGuides (rw : Rewrite) (amb : MVars.Ambient) : ExprSet := Id.run do
  let mut result := ∅
  result := result.union (subexprsWithoutMVars rw.lhs amb)
  result := result.union (subexprsWithoutMVars rw.rhs amb)
  for cond in rw.conds do result := result.union (subexprsWithoutMVars cond.type amb)
  return result

def genDerivedGuides (rws : Rewrites) (amb : MVars.Ambient) : MetaM Guides := do
  let guides : ExprSet := rws.foldl (init := ∅) (·.union <| deriveGuides · amb)
  let mut result := #[]
  for guide in guides, idx in [:guides.size] do
    result := result.push <| ← Guide.from guide (.guide idx (derived := true))
  return result
