import Egg.Core.Explanation.Basic
import Egg.Core.Explanation.Congr
import Egg.Core.Explanation.Parse.Basic
import Egg.Core.Explanation.Expr
import Egg.Core.Rewrite.Basic
import Egg.Core.Request.Equiv
import Egg.Core.Request.Term
open Lean Meta

namespace Egg.Proof

inductive Step.Rewrite where
  | rw    (rw : Egg.Rewrite) (isRefl : Bool)
  | defeq (src : Source)
  | reifiedEq
  | factAnd
  deriving Inhabited

def Step.Rewrite.isRefl : Rewrite → Bool
  | rw _ isRefl => isRefl
  | defeq _     => true
  -- TODO: This isn't necessarily true.
  | reifiedEq | factAnd => false

structure Step where
  lhs   : Expr
  rhs   : Expr
  proof : Expr
  rw    : Step.Rewrite
  dir   : Direction
  -- TODO: conds : Array Proof
  deriving Inhabited

inductive CongrStep where
  | rule (rw : Rewrite) (weakVars : Array (Nat × Nat))
  | reifiedEq (dir : Direction)

end Proof

abbrev Proof := Array Proof.Step

private def Proof.prove (prf : Proof) (cgr : Congr) : MetaM Expr := do
  let some first := prf[0]? | return (← cgr.rel.mkRefl cgr.lhs)
  unless ← isDefEq first.lhs cgr.lhs do
    fail s!"initial expression is not defeq to LHS of proof goal:\n\n  {first.lhs}\n\nvs\n\n  {cgr.lhs}"
  let mut proof := first.proof
  for step in prf[1:] do
    if !step.rw.isRefl then proof ← mkEqTrans proof step.proof
  unless ← isDefEq prf.back!.rhs cgr.rhs do fail "final expression is not defeq to rhs of proof goal"
  match cgr.rel with
  | .eq  => return proof
  | .iff => mkIffOfEq proof
where
  fail (msg : String) : MetaM Unit := do
    throwError s!"egg failed to build proof: {msg}"

mutual

private partial def Explanation.proof
    (expl : Explanation) (rws : Rewrites) (egraph : EGraph) (cfg : Config.Encoding)
    (conditionSubgoals : Bool) (fuel? : Option Nat := none) : MetaM Proof := do
  let mut current := expl.start
  let mut steps : Array Proof.Step := #[]
  for step in expl.steps, idx in [:expl.steps.size] do
    let next := step.dst
    let prf ← proofStep idx current next step.toInfo
    steps   := steps.push prf
    current := next
  for step in steps do synthLingeringTcErasureMVars step.rhs
  return steps
where
  fail {α} (msg : MessageData) (step? : Option Nat := none) : MetaM α := do
    let step := step?.map (s!" step {·}") |>.getD ""
    throwError m!"egg failed to build proof{step}: {msg}"

  proofStep (idx : Nat) (current next : Expr) (rwInfo : Rewrite.Info) : MetaM Proof.Step := do
    if let .factAnd := rwInfo.src then
      return {
        lhs := current, rhs := next, proof := ← mkFactAndStep idx current next,
        rw := .factAnd, dir := rwInfo.dir
      }
    if rwInfo.src.isDefEq then
      return {
        lhs := current, rhs := next, proof := ← mkReflStep idx current next rwInfo.src,
        rw := .defeq rwInfo.src, dir := rwInfo.dir
      }
    if let some rw := rws.find? rwInfo.src rwInfo.srcDir then
      -- TODO: Can there be conditional rfl proofs?
      if ← isRflProof rw.proof then
        return {
          lhs := current, rhs := next, proof := ← mkReflStep idx current next rwInfo.src,
          rw := .rw rw (isRefl := true), dir := rwInfo.dir
        }
      let prf ← mkCongrStep idx current next rwInfo.pos?.get! <| .rule (← rw.forDir rwInfo.dir) rwInfo.weakVars
      return {
        lhs := current, rhs := next, proof := prf, rw := .rw rw (isRefl := false), dir := rwInfo.dir
      }
    else if rwInfo.src.isReifiedEq then
      let prf ← mkCongrStep idx current next rwInfo.pos?.get! (.reifiedEq rwInfo.dir)
      return { lhs := current, rhs := next, proof := prf, rw := .reifiedEq, dir := rwInfo.dir }
    else
      fail s!"unknown rewrite {rwInfo.src.description}" idx

  mkReflStep (idx : Nat) (current next : Expr) (src : Source) : MetaM Expr := do
    unless ← isDefEq current next do
      fail s!"unification failure for proof by reflexivity with rw {src.description}" idx
    mkEqRefl next

  mkFactAndStep (idx : Nat) (current next : Expr) : MetaM Expr := do
    let .app (.app (.const ``And []) (.const ``True [])) (.const ``True []) := current
      | fail m!"invalid LHS of ∧-step from\n\n  '{current}'\nto\n  '{next}'" idx
    unless next.isTrue do fail m!"invalid RHS of ∧-step from\n\n  '{current}'\nto\n  '{next}'" idx
    mkAppM ``true_and #[.const ``True []]

  mkCongrStep (idx : Nat) (current next : Expr) (pos : SubExpr.Pos) (step : Proof.CongrStep) :
      MetaM Expr := do
    let mvc := (← getMCtx).mvarCounter
    let (lhs, rhs) ← placeCHoles idx current next pos step
    try (← mkCongrOf 0 mvc lhs rhs).eq
    catch err => fail m!"'mkCongrOf' failed with\n  {err.toMessageData}" idx

  placeCHoles (idx : Nat) (current next : Expr) (pos : SubExpr.Pos) (step : Proof.CongrStep) :
      MetaM (Expr × Expr) := do
    replaceSubexprs (root₁ := current) (root₂ := next) (p := pos) fun lhs rhs => do
      -- It's necessary that we create the fresh rewrite (that is, create the fresh mvars) in *this*
      -- local context as otherwise the mvars can't unify with variables under binders.
      match step with
      | .reifiedEq dir =>
        let proof ← proveReifiedEq idx lhs rhs dir
        return (
          ← mkCHole (forLhs := true) lhs proof,
          ← mkCHole (forLhs := false) rhs proof
        )
      | .rule rw weakVars =>
        let (rw, subst) ← rw.freshWithSubst
        let weakVars ← weakVars.mapM fun (m, node) => do
          let mvarId := MVarId.fromUniqueIdx m
          let some freshM := subst.expr[mvarId]?
            | fail m!"weak mvar {mvarId.name} does not appear in substitution {subst.expr.toList.map fun (m₁, m₂) => (m₁.name, m₂.name)}"
          return (freshM, node)
        unless ← isDefEq lhs rw.lhs do failIsDefEq "LHS" rw.src lhs rw.lhs rw.mvars.lhs current next idx
        unless ← isDefEq rhs rw.rhs do failIsDefEq "RHS" rw.src rhs rw.rhs rw.mvars.rhs current next idx
        for cond in rw.conds do
          if ← cond.mvar.isAssigned then continue
          let ⟨condKind, condMVar, condType⟩ := cond
          let condType ← instantiateMVars condType
          match condKind with
          | .proof =>
            if let some p ← proveCondition condType weakVars then
              unless ← isDefEq (.mvar condMVar) p do
                fail m!"proof of condition '{condType}' of rewrite {rw.src.description} was invalid" idx
            else if !conditionSubgoals then
              fail m!"condition '{condType}' of rewrite {rw.src.description} could not be proven" idx
          | .tcInst =>
            if let some p ← synthInstance? condType then
              unless ← isDefEq (.mvar condMVar) p do
                fail m!"synthesized type class for condition '{condType}' of rewrite {rw.src.description} was invalid" idx
            else if !conditionSubgoals then
              fail m!"type class condition '{condType}' of rewrite {rw.src.description} could not be synthesized" idx
        let proof ← rw.eqProof
        return (
          ← mkCHole (forLhs := true) lhs proof,
          ← mkCHole (forLhs := false) rhs proof
        )

  proveReifiedEq (idx : Nat) (current next : Expr) (dir : Direction) : MetaM Expr := do
    let (current, next) := match dir with
      | .forward  => (current, next)
      | .backward => (next, current)
    unless next.isTrue do
      fail m!"invalid RHS of reified equality step from\n\n  '{current}'\nto\n  '{next}'" idx
    let some (lhs, rhs) := current.eqOrIff?
      | fail m!"invalid LHS (not an equivalence) of reified equality step from\n\n  '{current}'\nto\n  '{next}'" idx
    unless ← isDefEq lhs rhs do
      fail m!"invalid LHS (not defeq) of reified equality step from\n\n  '{current}'\nto\n  '{next}'" idx
    match dir with
      | .forward  => mkEqTrue (← mkEqRefl lhs)
      | .backward => mkEqSymm <| ← mkEqTrue (← mkEqRefl lhs)

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

  proveCondition (cond : Expr) (weakVars : Array (MVarId × Nat)) : MetaM (Option Expr) := do
    if !conditionSubgoals then
      -- Assign unassigned weak mvars.
      let { result := lingeringMVars, .. } := cond.collectMVars {}
      for mvar in lingeringMVars do
        -- Skips ambient mvars.
        unless ← mvar.isAssignable do continue
        -- TODO: We have cases where conditions contain non-weak unassigned mvars, but it doesn't
        --       cause a problem.
        let some (_, enode) := weakVars.find? fun (m, _) => m == mvar | continue
        let term ← egraph.get { enode }
        unless ← isDefEq (.mvar mvar) term do
          fail m!"failed to assign term '{term}' to weak mvar {Expr.mvar mvar}"
    let cond ← instantiateMVars cond
    trace[egg.explanation] m!"Prove condition '{cond}'"
    let some prf ← mkSubproof cond (.const ``True []) | return none
    mkOfEqTrue prf

  mkSubproof (lhs rhs : Expr) : MetaM (Option Expr) := do
    if let some fuel := fuel? then unless fuel > 0 do fail "ran out of fuel"
    let req ← Request.Equiv.encoding lhs rhs cfg
    let some rawExpl := egraph.run req | return none
    withTraceNode `egg.explanation (fun _ => return m!"Nested Explanation for '{lhs}' = '{rhs}'") do
      trace[egg.explanation] rawExpl.str
    let expl ← rawExpl.parse
    expl.prove { lhs, rhs, rel := .eq } rws egraph cfg conditionSubgoals <| fuel?.map (· - 1)

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

partial def Explanation.prove'
    (expl : Explanation) (cgr : Congr) (rws : Rewrites) (egraph : EGraph) (cfg : Config.Encoding)
    (conditionSubgoals : Bool) (fuel? : Option Nat := none) : MetaM (Expr × Proof) := do
  let proof ← expl.proof rws egraph cfg conditionSubgoals fuel?
  match expl.kind with
  | .sameEClass => return (← proof.prove cgr, proof)
  | .eqTrue =>
    let eqTrueCgr : Congr := { lhs := ← cgr.expr, rhs := .const ``True [], rel := .eq }
    let p ← proof.prove eqTrueCgr
    return (← mkOfEqTrue p, proof)

partial def Explanation.prove
    (expl : Explanation) (cgr : Congr) (rws : Rewrites) (egraph : EGraph) (cfg : Config.Encoding)
    (conditionSubgoals : Bool) (fuel? : Option Nat := none) : MetaM Expr :=
  Prod.fst <$> expl.prove' cgr rws egraph cfg conditionSubgoals fuel?

end
