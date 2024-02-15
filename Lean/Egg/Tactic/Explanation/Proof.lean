import Egg.Core.Config
import Egg.Core.Explanation
open Lean Meta

-- TODO: Simplify tracing by adding `MessageData` instances for relevant types.

namespace Egg.Explanation

-- Note: Since we don't know lambda and forall expressions' binder types, we pass fresh mvars
--       instead. These are assigned in `Explanation.proof`.
--
-- Note: If universe level erasure is active, we don't know constant expressions' universe level
--       parameters. We can figure out how many there need to be though and instantiate them with
--       fresh universe level mvars.
def Expression.toExpr (cfg : Config) : Expression → MetaM Expr
  | bvar idx        => return .bvar idx
  | fvar id         => return .fvar id
  | mvar id         => return .mvar id
  | sort lvl        => return .sort lvl
  | const name lvls => mkConst name lvls.toList cfg.eraseULvls
  | app fn arg      => return .app (← toExpr cfg fn) (← toExpr cfg arg)
  | lam body        => return .lam .anonymous (← mkFreshExprMVar none) (← toExpr cfg body) .default
  | .forall body    => return .forallE .anonymous (← mkFreshExprMVar none) (← toExpr cfg body) .default
  | lit l           => return .lit l
where
  mkConst (name : Name) (lvls : List Level) (erasedULvls : Bool) : MetaM Expr := do
    if erasedULvls
    then mkConstWithFreshMVarLevels name
    else return .const name lvls

-- BUG: `isDefEq` doesn't unify level mvars.
def proof (expl : Explanation) (cgr : Congr) (rws : Rewrites) (cfg : Config) : MetaM Expr := do
  withTraceNode `egg.reconstruction (fun _ => return "Reconstruction") do
    let mut current ← expl.start.toExpr cfg
    let steps := expl.steps
    withTraceNode `egg.reconstruction (fun _ => return "Explanation") do
      trace[egg.reconstruction] current
      for step in steps, idx in [:steps.size] do
        withTraceNode `egg.reconstruction (fun _ => return s!"Step {idx}") do
          trace[egg.reconstruction] step.src.description
          trace[egg.reconstruction] ← step.dst.toExpr cfg
    unless ← isDefEq cgr.lhs current do
      throwError s!"{errorPrefix} initial expression is not defeq to lhs of proof goal"
    let mut proof ← mkEqRefl current
    for step in steps, idx in [:steps.size] do
      let next ← step.dst.toExpr cfg
      let stepEq ← do
        withTraceNode `egg.reconstruction (fun _ => return m!"Step {idx}") do
          trace[egg.reconstruction] m!"Current: {current}"
          trace[egg.reconstruction] m!"Next:    {next}"
          proofStep current next step.toInfo
      proof ← mkEqTrans proof stepEq
      current := next
    match cgr.rel with
    | .eq  => return proof
    | .iff => mkIffOfEq proof
where
  errorPrefix := "egg failed to reconstruct proof:"

  proofStep (current next : Expr) (rwInfo : Rewrite.Info) : MetaM Expr := do
    let some rw := rws.find? rwInfo.src | throwError s!"{errorPrefix} unknown rewrite"
    if (isRefl? rw.proof).isSome then
      unless ← isDefEq current next do throwError s!"{errorPrefix} unification failure for proof by reflexivity"
      mkEqRefl next
    else
      proofStepAux rwInfo.pos.toArray.toList current next (proofAtRw rwInfo.toDescriptor)

  proofStepAux (target : List Nat) (current next : Expr) (atTarget : Expr → Expr → MetaM Expr) : MetaM Expr := do
    let p :: tgt := target | atTarget current next
    match current, next, p with
    | .app fn₁ arg, .app fn₂ _, 0 =>
      let prf ← proofStepAux tgt fn₁ fn₂ atTarget
      let res ← mkCongrFun prf arg
      return res
    | .app fn arg₁, .app _ arg₂, 1 =>
      let prf ← proofStepAux tgt arg₁ arg₂ atTarget
      let res ← mkCongrArg fn prf
      return res
    | .lam _ ty b₁ _, .lam _ _ b₂ _, 1 =>
      withLocalDecl .anonymous .default ty fun fvar => do
        let b₁ := b₁.instantiate1 fvar
        let b₂ := b₂.instantiate1 fvar
        let prf ← proofStepAux tgt b₁ b₂ atTarget
        let res ← mkFunExt (← mkLambdaFVars #[fvar] prf)
        return res
    | .forallE _ ty b₁ _, .forallE _ _ b₂ _, 1 =>
      withLocalDecl .anonymous .default ty fun fvar => do
        let b₁ := b₁.instantiate1 fvar
        let b₂ := b₂.instantiate1 fvar
        let prf ← proofStepAux tgt b₁ b₂ atTarget
        mkForallCongr (← mkLambdaFVars #[fvar] prf)
    | _, _, _ => throwError s!"{errorPrefix} 'proofStepAux' received invalid arguments"

  proofAtRw (rwDesc : Rewrite.Descriptor) (current next : Expr) : MetaM Expr := do
    let some rw := rws.find? rwDesc.src | throwError s!"{errorPrefix} unknown rewrite"
    let freshRw ← (← rw.fresh).forDir rwDesc.dir
    withTraceNode `egg.reconstruction (fun _ => return m!"Rewrite {rwDesc.src.description}") do
      trace[egg.reconstruction] m!"Type: {freshRw.lhs} = {freshRw.rhs}"
      trace[egg.reconstruction] m!"Proof: {freshRw.proof}"
      trace[egg.reconstruction] m!"Holes: {freshRw.holes.map (Expr.mvar ·)}"
    withTraceNode `egg.reconstruction (fun _ => return m!"Unification") do
      withTraceNode `egg.reconstruction (fun _ => return "LHS") (collapsed := false) do
        trace[egg.reconstruction] current
        trace[egg.reconstruction] freshRw.lhs
      withTraceNode `egg.reconstruction (fun _ => return "RHS") (collapsed := false) do
        trace[egg.reconstruction] next
        trace[egg.reconstruction] freshRw.rhs
    unless ← isDefEq current freshRw.lhs <&&> isDefEq next freshRw.rhs do
      throwError s!"{errorPrefix} unification failure"
    match freshRw.rel with
    | .eq  => return freshRw.proof
    | .iff => mkPropExt freshRw.proof
