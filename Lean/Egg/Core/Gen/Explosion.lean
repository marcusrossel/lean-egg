import Egg.Core.Premise.Rewrites
import Lean
open Lean Meta

-- From https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/sorting.20in.20monad/near/473162379
private partial def List.qsortM [Monad m] (comp : α → α → m Bool) [BEq α] : List α → m (List α )
  | [] => return []
  | x :: xs => do
    let (fst, lst) ← xs.partitionM fun t => comp t x
    return (← fst.qsortM comp) ++ [x] ++ (← lst.qsortM comp)

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

private partial def genExplosionsForRw (rw : Rewrite) : MetaM Rewrites := do
  let missingOnLhs := rw.mvars.rhs.expr.subtract rw.mvars.lhs.expr
  let missingOnRhs := rw.mvars.lhs.expr.subtract rw.mvars.rhs.expr
  return (← genDir .forward  missingOnLhs) ++ (← genDir .backward missingOnRhs)
where
  genDir (dir : Direction) (missing : MVarIdSet) : MetaM Rewrites := do
    unless !missing.isEmpty do return #[]
    let ordered ← missing.toList.qsortM fun m₁ m₂ => return !(← exprReferencesMVar (.mvar m₁) m₂)
    core rw dir ordered []
  core (rw : Rewrite) (dir : Direction) (missing : List MVarId) (loc : List Nat) :
      MetaM Rewrites := do
    let m :: miss := missing | return #[← rw.fresh (src := .explosion rw.src dir loc)]
    let lctx ← getLCtx
    let mut minIdx := 0
    let mut explosions : Rewrites := #[]
    while minIdx < lctx.decls.size do
      let (fresh, subst) ← rw.freshWithSubst
      let m := subst.expr.fwd[m]!
      let some (fvar, idx) ← findLocalDeclWithTypeMinIdx? (← m.getType) minIdx | break
      minIdx := idx + 1
      unless ← isDefEq (.mvar m) (.fvar fvar) do throwError "egg: internal error in explosion gen"
      let fresh ← fresh.instantiateMVars
      let miss := miss.filterMap fun i =>
        let i' := subst.expr.fwd[i]!
        if fresh.mvars.lhs.expr.contains i' || fresh.mvars.rhs.expr.contains i' then i' else none
      explosions := explosions ++ (← core fresh dir miss <| loc ++ [minIdx])
    return explosions

def genExplosions (targets : Rewrites) : MetaM Rewrites := do
  targets.foldlM (init := #[]) fun acc rw => return acc ++ (← genExplosionsForRw rw)
