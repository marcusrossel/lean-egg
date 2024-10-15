import Egg.Core.Explanation.Basic
import Egg.Core.Explanation.Congr
import Egg.Core.Explanation.Expr
import Egg.Core.Explanation.Flatten
import Egg.Core.Explanation.Parse
import Egg.Core.Premise.Rewrites
import Egg.Core.Premise.Facts
import Egg.Core.Request.Equiv
open Lean Meta

namespace Egg.Proof

abbrev Subgoals := List MVarId

inductive Step.Rewrite where
  | rw    (rw : Egg.Rewrite) (isRefl : Bool)
  | defeq (src : Source)
  deriving Inhabited

def Step.Rewrite.isRefl : Rewrite → Bool
  | rw _ isRefl => isRefl
  | defeq _     => true

structure Step where
  lhs   : Expr
  rhs   : Expr
  proof : Expr
  rw    : Step.Rewrite
  dir   : Direction
  -- TODO: conds : Array Proof
  deriving Inhabited

end Proof

structure Proof where
  steps    : Array Proof.Step
  subgoals : Proof.Subgoals

def Proof.prove (prf : Proof) (cgr : Congr) : MetaM Expr := do
  let some first := prf.steps[0]? | return (← cgr.rel.mkRefl cgr.lhs)
  unless ← isDefEq first.lhs cgr.lhs do fail "initial expression is not defeq to lhs of proof goal"
  let mut proof := first.proof
  for step in prf.steps[1:] do
    if !step.rw.isRefl then proof ← mkEqTrans proof step.proof
  unless ← isDefEq prf.steps.back.rhs cgr.rhs do fail "final expression is not defeq to rhs of proof goal"
  match cgr.rel with
  | .eq  => return proof
  | .iff => mkIffOfEq proof
where
  fail (msg : String) : MetaM Unit := do
    throwError s!"egg failed to build proof: {msg}"

partial def Explanation.proof
    (expl : Explanation) (rws : Rewrites) (facts : Facts) (egraph : EGraph) (ctx : EncodingCtx) :
    MetaM Proof := do
  let mut current ← expl.start.toExpr
  let mut steps    : Array Proof.Step := #[]
  let mut subgoals : Proof.Subgoals := []
  for step in expl.steps do
    let next ← step.dst.toExpr
    let (prf, sub) ← proofStep current next step
    steps    := steps.push prf
    subgoals := subgoals ++ sub
    current  := next
  return { steps, subgoals }
where
  fail {α} (msg : MessageData) : MetaM α := do
    throwError m!"egg failed to build proof: {msg}"

  proofStep (current next : Expr) (step : Step) : MetaM (Proof.Step × Proof.Subgoals) := do
    if step.src.isDefEq then
      let step := {
        lhs := current, rhs := next, proof := ← mkReflStep current next step.toDescriptor,
        rw := .defeq step.src, dir := step.dir
      }
      return (step, [])
    let some rw := rws.find? step.src | fail s!"unknown rewrite {step.src.description}"
    -- TODO: Can there be conditional rfl proofs?
    if ← isRflProof rw.proof then
      let step := {
        lhs := current, rhs := next, proof := ← mkReflStep current next step.toDescriptor,
        rw := .rw rw (isRefl := true), dir := step.dir
      }
      return (step, [])
    let facts ← step.facts.mapM fun src? => do
      let some src := src? | pure none
      facts.find? (·.src == src) |>.getDM <| fail m!"explanation references unknown fact {src}"
    let (prf, subgoals) ← mkCongrStep current next step.pos (← rw.forDir step.dir) facts
    let step := {
      lhs := current, rhs := next, proof := prf,
      rw := .rw rw (isRefl := false), dir := step.dir
    }
    return (step, subgoals)

  mkReflStep (current next : Expr) (rw : Rewrite.Descriptor) : MetaM Expr := do
    unless ← isDefEq current next do
      fail s!"unification failure for proof by reflexivity with rw {rw.src.description}"
    mkEqRefl next

  mkCongrStep (current next : Expr) (pos : SubExpr.Pos) (rw : Rewrite) (facts : Array (Option Fact)) :
      MetaM (Expr × Proof.Subgoals) := do
    let mvc := (← getMCtx).mvarCounter
    let (lhs, rhs, subgoals) ← placeCHoles current next pos rw facts
    try return (← (← mkCongrOf 0 mvc lhs rhs).eq, subgoals)
    catch err => fail m!"'mkCongrOf' failed with\n  {err.toMessageData}"

  placeCHoles (current next : Expr) (pos : SubExpr.Pos) (rw : Rewrite) (facts : Array (Option Fact)) :
      MetaM (Expr × Expr × Proof.Subgoals) := do
    replaceSubexprs (root₁ := current) (root₂ := next) (p := pos) fun lhs rhs => do
      -- It's necessary that we create the fresh rewrite (that is, create the fresh mvars) in *this*
      -- local context as otherwise the mvars can't unify with variables under binders.
      let rw ← rw.fresh
      unless ← isDefEq lhs rw.lhs do fail m!"unification failure for LHS of rewrite {rw.src.description}:\n  {lhs}\nvs\n  {rw.lhs}\nin\n  {current}\nand\n  {next}"
      unless ← isDefEq rhs rw.rhs do fail m!"unification failure for RHS of rewrite {rw.src.description}:\n  {rhs}\nvs\n  {rw.rhs}\nin\n  {current}\nand\n  {next}"
      let mut subgoals := []
      let conds := rw.conds.filter (!·.isProven)
      for cond in conds, fact? in facts do
        if let some fact := fact? then
          if ← isDefEq cond.expr fact.proof then
            continue
          else
            if let some condProof ← mkConditionSubproof fact cond.type then
              if ← isDefEq cond.expr condProof then continue
            fail m!"condition {cond.type} of rewrite {rw.src.description} could not be proven"
        else
          subgoals := subgoals.concat cond.expr.mvarId!
      let proof ← rw.eqProof
      return (
        ← mkCHole (forLhs := true) lhs proof,
        ← mkCHole (forLhs := false) rhs proof,
        subgoals
      )

  mkConditionSubproof (fact : Fact) (cond : Expr) : MetaM (Option Expr) := do
    let rawExpl := egraph.run (← Request.Equiv.encoding fact.type cond ctx)
    if rawExpl.isEmpty then return none
    let expl ← rawExpl.parse
    let proof ← expl.proof rws facts egraph ctx
    let factEqCond ← proof.prove { lhs := fact.type, rhs := cond, rel := .eq }
    mkEqMP factEqCond fact.proof
