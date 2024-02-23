 import Egg.Core.Explanation.Basic
import Egg.Core.Explanation.Congr
import Egg.Core.Rewrites.Basic
open Lean Meta

-- TODO: Simplify tracing by adding `MessageData` instances for relevant types.

namespace Egg.Explanation

def Expression.toExpr : Expression → MetaM Expr
  | bvar idx        => return .bvar idx
  | fvar id         => return .fvar id
  | mvar id         => return .mvar id
  | sort lvl        => return .sort lvl
  | const name lvls => return .const name lvls
  | app fn arg      => return .app (← toExpr fn) (← toExpr arg)
  | lam ty body     => return .lam .anonymous (← toExpr ty) (← toExpr body) .default
  | .forall ty body => return .forallE .anonymous (← toExpr ty) (← toExpr body) .default
  | lit l           => return .lit l
  | erased          => mkFreshExprMVar none

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
        let mvarCounterSaved := (← getMCtx).mvarCounter
        let (lhs, rhs) ← placeRwCHoles current next rwInfo
        let res ← mkCongrOf 0 mvarCounterSaved lhs rhs
        res.eq

  mkReflStep (current next : Expr) : MetaM Expr := do
    unless ← isDefEq current next do throwError s!"{errorPrefix} unification failure for proof by reflexivity"
    mkEqRefl next

  placeRwCHoles (current next : Expr) (rwInfo : Rewrite.Info) : MetaM (Expr × Expr) := do
    replaceSubexprs (root₁ := current) (root₂ := next) (p := rwInfo.pos) fun lhs rhs => do
      let some rw := rws.find? rwInfo.src | throwError s!"{errorPrefix} unknown rewrite"
      let proof ← (← (← rw.fresh).forDir rwInfo.dir).eqProof
      return (
        ← mkCHole (forLhs := true) lhs proof,
        ← mkCHole (forLhs := false) rhs proof
      )
