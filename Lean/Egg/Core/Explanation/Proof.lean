import Egg.Core.Explanation.Basic
import Egg.Core.Explanation.Congr
import Egg.Core.Explanation.Parse.Basic
import Egg.Core.Explanation.Expr
import Egg.Core.Premise.Rewrites
import Egg.Core.Request.Equiv
open Lean Meta

namespace Egg.Proof

abbrev Subgoals := List MVarId

inductive Step.Rewrite where
  | rw    (rw : Egg.Rewrite) (isRefl : Bool)
  | defeq (src : Source)
  | reifiedEq
  deriving Inhabited

def Step.Rewrite.isRefl : Rewrite → Bool
  | rw _ isRefl => isRefl
  | defeq _     => true
  -- TODO: This isn't necessarily true.
  | reifiedEq => false

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
  unless ← isDefEq prf.steps.back!.rhs cgr.rhs do fail "final expression is not defeq to rhs of proof goal"
  match cgr.rel with
  | .eq  => return proof
  | .iff => mkIffOfEq proof
where
  fail (msg : String) : MetaM Unit := do
    throwError s!"egg failed to build proof: {msg}"

partial def Explanation.proof
    (expl : Explanation) (rws : Rewrites) (egraph : EGraph) (ctx : EncodingCtx) :
    MetaM Proof := do
  let mut current := expl.start
  let mut steps : Array Proof.Step := #[]
  let mut subgoals : Proof.Subgoals := []
  for step in expl.steps, idx in [:expl.steps.size] do
    let next := step.dst
    let (prf, sub) ← proofStep idx current next step.toInfo
    steps    := steps.push prf
    subgoals := subgoals ++ sub
    current  := next
  for step in steps do synthLingeringTcErasureMVars step.rhs
  return { steps, subgoals }
where
  fail {α} (msg : MessageData) (step? : Option Nat := none) : MetaM α := do
    let step := step?.map (s!" step {·}") |>.getD ""
    throwError m!"egg failed to build proof{step}: {msg}"

  proofStep (idx : Nat) (current next : Expr) (rwInfo : Rewrite.Info) :
      MetaM (Proof.Step × Proof.Subgoals) := do
    if let .reifiedEq := rwInfo.src then
      let step := {
        lhs := current, rhs := next, proof := ← mkReifiedEqStep idx current next,
        rw := .reifiedEq, dir := rwInfo.dir
      }
      return (step, [])
    if rwInfo.src.isDefEq then
      let step := {
        lhs := current, rhs := next, proof := ← mkReflStep idx current next rwInfo.src,
        rw := .defeq rwInfo.src, dir := rwInfo.dir
      }
      return (step, [])
    let some rw := rws.find? rwInfo.src | fail s!"unknown rewrite {rwInfo.src.description}" idx
    -- TODO: Can there be conditional rfl proofs?
    if ← isRflProof rw.proof then
      let step := {
        lhs := current, rhs := next, proof := ← mkReflStep idx current next rwInfo.src,
        rw := .rw rw (isRefl := true), dir := rwInfo.dir
      }
      return (step, [])
    let (prf, subgoals) ← mkCongrStep idx current next rwInfo.pos?.get! (← rw.forDir rwInfo.dir)
    let step := {
      lhs := current, rhs := next, proof := prf, rw := .rw rw (isRefl := false), dir := rwInfo.dir
    }
    return (step, subgoals)

  mkReflStep (idx : Nat) (current next : Expr) (src : Source) : MetaM Expr := do
    unless ← isDefEq current next do
      fail s!"unification failure for proof by reflexivity with rw {src.description}" idx
    mkEqRefl next

  mkReifiedEqStep (idx : Nat) (current next : Expr) : MetaM Expr := do
    unless next.isTrue do
      fail "invalid RHS of reified equality step from\n\n  '{current}'\to\n  '{next}'" idx
    let some (lhs, rhs) := current.eqOrIff?
      | fail "invalid LHS of reified equality step from\n\n  '{current}'\to\n  '{next}'" idx
    unless ← isDefEq lhs rhs do
      fail "invalid LHS of reified equality step from\n\n  '{current}'\to\n  '{next}'" idx
    mkEqTrue (← mkEqRefl lhs)
    /- This loops, and I think reified eq-steps might always be by refl, because we only introduce
       a union by reified eq for fresh e-classes.

      ```
      let some prf ← mkSubproof current next
        |  fail m!"reified equality '{current} = {next}' could not be proven" idx
      return prf
      ```
    -/

  mkCongrStep (idx : Nat) (current next : Expr) (pos : SubExpr.Pos) (rw : Rewrite) :
      MetaM (Expr × Proof.Subgoals) := do
    let mvc := (← getMCtx).mvarCounter
    let (lhs, rhs, subgoals) ← placeCHoles idx current next pos rw
    try return (← (← mkCongrOf 0 mvc lhs rhs).eq, subgoals)
    catch err => fail m!"'mkCongrOf' failed with\n  {err.toMessageData}" idx

  placeCHoles (idx : Nat) (current next : Expr) (pos : SubExpr.Pos) (rw : Rewrite) :
      MetaM (Expr × Expr × Proof.Subgoals) := do
    replaceSubexprs (root₁ := current) (root₂ := next) (p := pos) fun lhs rhs => do
      -- It's necessary that we create the fresh rewrite (that is, create the fresh mvars) in *this*
      -- local context as otherwise the mvars can't unify with variables under binders.
      let rw ← rw.fresh
      unless ← isDefEq lhs rw.lhs do failIsDefEq "LHS" rw.src lhs rw.lhs rw.mvars.lhs current next idx
      /- TODO: Remove?
        let lhsType ← inferType lhs
        let rwLhsType ← inferType rw.lhs
        let _ ← isDefEq lhsType rwLhsType
        synthLingeringTcErasureMVars lhs
        synthLingeringTcErasureMVars rw.lhs
        unless ← isDefEq lhs rw.lhs do
          failIsDefEq "LHS" rw.src lhs rw.lhs rw.mvars.lhs.expr current next idx
      -/
      unless ← isDefEq rhs rw.rhs do failIsDefEq "RHS" rw.src rhs rw.rhs rw.mvars.rhs current next idx
      let mut subgoals := []
      let conds := rw.conds.filter (!·.isProven)
      for cond in conds do
        match cond.kind with
        | .proof =>
          let cond ← cond.instantiateMVars
          let some p ← proveCondition cond.type
            | fail m!"condition '{cond.type}' of rewrite {rw.src.description} could not be proven" idx
          unless ← isDefEq cond.expr p do
            fail m!"proof of condition '{cond.type}' of rewrite {rw.src.description} was invalid" idx
        | .tcInst =>
          fail m!"type class conditions aren't implemented yet: '{cond.type}' of rewrite {rw.src.description}" idx
      let proof ← rw.eqProof
      return (
        ← mkCHole (forLhs := true) lhs proof,
        ← mkCHole (forLhs := false) rhs proof,
        subgoals
      )

  failIsDefEq
      {α} (side : String) (src : Source) (expr rwExpr : Expr) (rwMVars : MVars)
      (current next : Expr) (idx : Nat) : MetaM α := do
    let expr   ← instantiateMVars expr
    let rwExpr ← instantiateMVars rwExpr
    let mut readOnlyOrSynthOpaque := []
    let mut types := "\n"
    -- TODO: Improve this by showing the MVars.Properties of mvars.
    for mvar in rwMVars.expr.keys do
      if ← mvar.isReadOnlyOrSyntheticOpaque then readOnlyOrSynthOpaque := readOnlyOrSynthOpaque.concat mvar
      types := types ++ s!"  {← ppExpr (.mvar mvar)}: {← ppExpr <| ← mvar.getType}\n"
    fail m!"unification failure for {side} of rewrite {src.description}:\n\n  {expr}\nvs\n  {rwExpr}\nin\n  {current}\nand\n  {next}\n\n• Types: {types}\n• Read Only Or Synthetic Opaque MVars: {readOnlyOrSynthOpaque}" idx

  proveCondition (cond : Expr) : MetaM (Option Expr) := do
    let some prf ← mkSubproof cond (.const ``True []) | return none
    mkOfEqTrue prf

  mkSubproof (lhs rhs : Expr) : MetaM (Option Expr) := do
    let req ← Request.Equiv.encoding lhs rhs ctx
    let rawExpl := egraph.run req
    if rawExpl.str.isEmpty then return none
    let expl ← rawExpl.parse
    let proof ← expl.proof rws egraph ctx
    proof.prove { lhs, rhs, rel := .eq }

  synthLingeringTcErasureMVars (e : Expr) : MetaM Unit := do
    let mvars := (← instantiateMVars e).collectMVars {} |>.result
    for mvar in mvars do
      let type ← mvar.getType
      unless (← isClass? type).isSome do continue
      let inst? ← do
        if let some inst ← findLocalDeclWithType? type
        then pure <| some (.fvar inst)
        else optional (synthInstance type)
      let some inst := inst? | continue
      unless ← isDefEq (.mvar mvar) inst do
        throwError "egg: internal error in 'Egg.Proof.Explanation.proof.synthLingeringTcErasureMVars'"
