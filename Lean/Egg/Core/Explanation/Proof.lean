import Egg.Core.Explanation.Basic
import Egg.Core.Rewrites.Basic
open Lean Meta

-- TODO: Simplify tracing by adding `MessageData` instances for relevant types.

namespace Egg.Explanation

def Expression.toExpr : Expression → MetaM Expr
  | bvar idx               => return .bvar idx
  | fvar id                => return .fvar id
  | mvar id                => return .mvar id
  | sort lvl               => return .sort lvl
  | const name none        => mkConstWithFreshMVarLevels name
  | const name (some lvls) => return .const name lvls.toList
  | app fn arg             => return .app (← toExpr fn) (← toExpr arg)
  | lam ty body            => return .lam .anonymous (← toExpr ty) (← toExpr body) .default
  | .forall ty body        => return .forallE .anonymous (← toExpr ty) (← toExpr body) .default
  | lit l                  => return .lit l
  | erased                 => mkFreshExprMVar none

-- BUG: `isDefEq` doesn't unify level mvars.
def proof (expl : Explanation) (cgr : Congr) (rws : Rewrites) : MetaM Expr := do
  withTraceNode `egg.reconstruction (fun _ => return "Reconstruction") do
    let mut current ← expl.start.toExpr
    let steps := expl.steps
    withTraceNode `egg.reconstruction (fun _ => return "Explanation") do
      trace[egg.reconstruction] current
      for step in steps, idx in [:steps.size] do
        withTraceNode `egg.reconstruction (fun _ => return s!"Step {idx}") do
          trace[egg.reconstruction] step.src.description
          trace[egg.reconstruction] ← step.dst.toExpr
    unless ← isDefEq cgr.lhs current do
      throwError s!"{errorPrefix} initial expression is not defeq to lhs of proof goal"
    let mut proof ← mkEqRefl current
    for step in steps, idx in [:steps.size] do
      let next ← step.dst.toExpr
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
    if rwInfo.src.isNatLit then
      mkReflStep current next
    else
      let some rw := rws.find? rwInfo.src | throwError s!"{errorPrefix} unknown rewrite"
      if (isRefl? rw.proof).isSome then
        mkReflStep current next
      else
        proofStepAux rwInfo.pos.toArray.toList current next (proofAtRw rwInfo.toDescriptor)

  mkReflStep (current next : Expr) : MetaM Expr := do
    unless ← isDefEq current next do throwError s!"{errorPrefix} unification failure for proof by reflexivity"
    mkEqRefl next

  proofStepAux (target : List Nat) (current next : Expr) (atTarget : Expr → Expr → MetaM Expr) : MetaM Expr := do
    let p :: tgt := target | atTarget current next
    match current, next, p with
    | .app fn₁ arg, .app fn₂ _, 0 =>
      let prf ← proofStepAux tgt fn₁ fn₂ atTarget
      mkCongrFun prf arg
    | .app fn arg₁, .app _ arg₂, 1 =>
      let prf ← proofStepAux tgt arg₁ arg₂ atTarget
      mkCongrArg fn prf
    | .lam _ ty b₁ _, .lam _ _ b₂ _, 1 =>
      withLocalDecl .anonymous .default ty fun fvar => do
        let b₁ := b₁.instantiate1 fvar
        let b₂ := b₂.instantiate1 fvar
        let prf ← proofStepAux tgt b₁ b₂ atTarget
        mkFunExt (← mkLambdaFVars #[fvar] prf)
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
