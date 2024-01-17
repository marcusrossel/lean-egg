import Egg.Core.Explanation
open Lean Meta

namespace Egg.Explanation

-- Note: Since we don't know lambda expressions' binder types, we pass fresh mvars instead. These
--       are assigned in `Explanation.proof`.
def Expression.toExpr : Expression → MetaM Expr
  | bvar idx          => return .bvar idx
  | fvar id           => return .fvar id
  | mvar id           => return .mvar id
  | sort lvl          => return .sort lvl
  | const name lvls   => return .const name lvls.toList
  | app fn arg        => return .app (← toExpr fn) (← toExpr arg)
  | lam body          => return .lam .anonymous (← mkFreshExprMVar none) (← toExpr body) .default
  | .forall type body => return .forallE .anonymous (← toExpr type) (← toExpr body) .default
  | lit l             => return .lit l

private def errorPrefix :=
  "'egg' tactic failed to reconstruct proof:"

-- TODO: The initial `current` might need to be the original lhs expression of the equality we're
--       trying to prove, so that we get the types of lambda binder mvars. In that case, we should
--       still check that its defeq to `expl.start.toExpr` though.
def proof (expl : Explanation) (rel : Relation) (rws : Rewrites) : MetaM Expr := do
  let mut current ← expl.start.toExpr
  let mut proof ← mkEqRefl current
  for step in expl.steps do
    let next ← step.dst.toExpr
    let stepEq ← proofStep current next step.toInfo
    proof ← mkEqTrans proof stepEq
    current := next
  match rel with
  | .eq  => return proof
  | .iff => mkIffOfEq proof
where
  proofStep (current next : Expr) (rwInfo : Rewrite.Info) : MetaM Expr := do
    let eqAtRw ← proofStepAtRwPos current next rwInfo
    let motive ← mkMotive current rwInfo.pos
    mkEqNDRec motive (← mkEqRefl current) eqAtRw

  proofStepAtRwPos (current next : Expr) (rwInfo : Rewrite.Info) : MetaM Expr := do
    viewSubexpr (p := rwInfo.pos) (root := next) fun _ rhs => do
      viewSubexpr (p := rwInfo.pos) (root := current) fun _ lhs => do
        let some rw := rws.find? rwInfo.src | throwError s!"{errorPrefix} unknown rewrite"
        let rw ← (← rw.fresh).forDir rwInfo.dir
        unless ← isDefEq lhs rw.lhs do throwError s!"{errorPrefix} rewrite's lhs is not defeq to required type"
        unless ← isDefEq rhs rw.rhs do throwError s!"{errorPrefix} rewrite's rhs is not defeq to required type"
        match rw.rel with
        | .eq  => return rw.proof
        | .iff => mkPropExt rw.proof

  mkMotive (lhs : Expr) (pos : SubExpr.Pos) : MetaM Expr :=
    viewSubexpr (p := pos) (root := lhs) fun _ target => do
      withLocalDecl .anonymous .default (← inferType target) fun fvar => do
        let rhs ← replaceSubexpr (fun _ => return fvar) pos lhs
        mkLambdaFVars #[fvar] (← mkEq lhs rhs)
