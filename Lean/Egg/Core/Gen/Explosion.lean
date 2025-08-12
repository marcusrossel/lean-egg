import Egg.Core.Rewrite.Rule
import Lean
open Lean Meta

private def Lean.Meta.findLocalDeclWithTypeMinIdx? (type : Expr) (minIdx : Nat) :
    MetaM <| Option (FVarId × Nat) := do
  let decls := (← getLCtx).decls
  for h : idx in [minIdx:decls.size] do
    let some decl := decls[idx] | continue
    if ← isDefEq type decl.type then return some (decl.fvarId, idx)
  return none

namespace Egg

private partial def exprReferencesMVar (e : Expr) (m : MVarId) : MetaM Bool := do
  if e.isSort then
    return false
  else
    match e with
    | .mvar id => if id == m then return true
    | .app e₁ e₂ | .lam _ e₁ e₂ _ | .forallE _ e₁ e₂ _ =>
      if ← exprReferencesMVar e₁ m <||> exprReferencesMVar e₂ m then return true
    | _ => pure ()
    exprReferencesMVar (← inferType e) m

private partial def genExplosionsForRw
    (rw : Rewrite) (id : Rewrite.Rule.Id) (subgoals : Bool) : MetaM Rewrite.Rules := do
  let mut missing := rw.mvars.rhs.visibleExpr.subtract rw.mvars.lhs.visibleExpr
  for violation in ← rw.violations subgoals do
    if let .lhsSingleMVar m := violation then
      missing := missing.insert m
      break
  if missing.isEmpty then return ∅
  let ordered ← missing.toList.qsortM fun m₁ m₂ => return !(← exprReferencesMVar (.mvar m₁) m₂)
  core rw ordered []
where
  core (rw : Rewrite) (missing : List MVarId) (loc : List Nat) : MetaM Rewrite.Rules := do
    let m :: miss := missing |
      let id := { id with src := .explosion id.src loc }
      return {⟨id, ← rw.fresh⟩}
    let mut minIdx := 0
    let mut explosions := ∅
    while minIdx < (← getLCtx).decls.size do
      let (fresh, subst) ← rw.freshWithSubst
      let m := subst.expr[m]!
      let some (fvar, idx) ← findLocalDeclWithTypeMinIdx? (← m.getType) minIdx | break
      minIdx := idx + 1
      unless ← isDefEq (.mvar m) (.fvar fvar) do throwError "egg: internal error in explosion gen"
      let fresh ← fresh.instantiateMVars
      unless fresh.conds.unsynthesizable.isEmpty do continue
      let miss := miss.filterMap fun i =>
        let i' := subst.expr[i]!
        if fresh.mvars.lhs.expr.contains i' || fresh.mvars.rhs.expr.contains i' then i' else none
      explosions := explosions ∪ (← core fresh miss <| loc ++ [minIdx])
    return explosions

def genExplosions (rules : Rewrite.Rules) (subgoals : Bool) : MetaM Rewrite.Rules := do
  let mut explosions := ∅
  for rule in rules.entries do
    let new ← genExplosionsForRw rule.rw rule.id subgoals
    explosions := explosions ∪ new
  return explosions
