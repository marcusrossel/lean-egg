 import Egg.Core.Explanation.Basic
import Egg.Core.Explanation.Congr
import Egg.Core.Rewrites.Basic
open Lean Meta

-- TODO: Simplify tracing by adding `MessageData` instances for relevant types.

namespace Egg.Explanation

private partial def replaceSubexprs
    (replace : (sub₁ sub₂ : Expr) → MetaM (Expr × Expr)) (p : SubExpr.Pos) (root₁ root₂ : Expr) :
    MetaM (Expr × Expr) :=
  go replace p.toArray.toList root₁ root₂
where
  go (g : Expr → Expr → MetaM (Expr × Expr)) : List Nat → Expr → Expr → MetaM (Expr × Expr)
    | [],       e₁, e₂ => g e₁ e₂
    | hd :: tl, e₁, e₂ => coord (go g tl) hd e₁ e₂

  coord (g : Expr → Expr → MetaM (Expr × Expr)) (c : Nat) (e₁ e₂ : Expr) : MetaM (Expr × Expr) := do
    match c, e₁, e₂ with
    | 0, .app f₁ a₁, .app f₂ a₂ => do
      unless ← isDefEq a₁ a₂ do throwDifferent e₁ e₂
      let (f₁', f₂') ← g f₁ f₂
      return (.app f₁' a₁, .app f₂' a₂)
    | 1, .app f₁ a₁, .app f₂ a₂ => do
      unless ← isDefEq f₁ f₂ do throwDifferent e₁ e₂
      let (a₁', a₂') ← g a₁ a₂
      return (.app f₁ a₁', .app f₂ a₂')
    | 0, .lam n₁ t₁ b₁ i₁, .lam n₂ t₂ b₂ i₂ => do
      unless ← isDefEq b₁ b₂ do throwDifferent e₁ e₂
      let (t₁', t₂') ← g t₁ t₂
      return (.lam n₁ t₁' b₁ i₁, .lam n₂ t₂' b₂ i₂)
    | 1, .lam n₁ t₁ b₁ i₁, .lam _ t₂ b₂ _ => do
      unless ← isDefEq t₁ t₂ do throwDifferent e₁ e₂
      withLocalDecl n₁ i₁ t₁ fun fvar => do
        let (b₁', b₂') ← g (b₁.instantiateRev #[fvar]) (b₂.instantiateRev #[fvar])
        return (← mkLambdaFVars #[fvar] b₁', ← mkLambdaFVars #[fvar] b₂')
    | 0, .forallE n₁ t₁ b₁ i₁, .forallE n₂ t₂ b₂ i₂ => do
      unless ← isDefEq b₁ b₂ do throwDifferent e₁ e₂
      let (t₁', t₂') ← g t₁ t₂
      return (.forallE n₁ t₁' b₁ i₁, .forallE n₂ t₂' b₂ i₂)
    | 1, .forallE n₁ t₁ b₁ i₁, .forallE _ t₂ b₂ _ => do
      unless ← isDefEq t₁ t₂ do throwDifferent e₁ e₂
      withLocalDecl n₁ i₁ t₁ fun fvar => do
        let (b₁', b₂') ← g (b₁.instantiateRev #[fvar]) (b₂.instantiateRev #[fvar])
        return (← mkForallFVars #[fvar] b₁', ← mkForallFVars #[fvar] b₂')
    | 0, .letE n₁ t₁ v₁ b₁ f₁, .letE n₂ t₂ v₂ b₂ f₂ => do
      unless ← isDefEq v₁ v₂ <&&> isDefEq b₁ b₂ do throwDifferent e₁ e₂
      let (t₁', t₂') ← g t₁ t₂
      return (.letE n₁ t₁' v₁ b₁ f₁, .letE n₂ t₂' v₂ b₂ f₂)
    | 1, .letE n₁ t₁ v₁ b₁ f₁, .letE n₂ t₂ v₂ b₂ f₂ => do
      unless ← isDefEq t₁ t₂ <&&> isDefEq b₁ b₂ do throwDifferent e₁ e₂
      let (v₁', v₂') ← g v₁ v₂
      return (.letE n₁ t₁ v₁' b₁ f₁, .letE n₂ t₂ v₂' b₂ f₂)
    | 2, .letE n₁ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ => do
      unless ← isDefEq t₁ t₂ <&&> isDefEq v₁ v₂ do throwDifferent e₁ e₂
      withLetDecl n₁ t₁ v₁ fun fvar => do
        let (b₁', b₂') ← g (b₁.instantiateRev #[fvar]) (b₂.instantiateRev #[fvar])
        return (← mkLetFVars #[fvar] b₁', ← mkLetFVars #[fvar] b₂')
    | 0, .proj t₁ i₁ s₁, .proj t₂ i₂ s₂ => do
      unless t₁ == t₂ && i₁ == i₂ do throwDifferent e₁ e₂
      let (s₁', s₂') ← g s₁ s₂
      return (.proj t₁ i₁ s₁', .proj t₂ i₂ s₂')
    | n, .mdata d₁ e₁, .mdata d₂ e₂ => do
      let (e₁', e₂') ← coord g n e₁ e₂
      return (.mdata d₁ e₁', .mdata d₂ e₂')
    | 3, _, _ =>
      throwError "'Egg.Explanation.replaceSubexprs' tried to lens on types (this is not supported)"
    | n, e₁@(.mvar _), e₂ => do
      unless ← isDefEq e₁ e₂ do throwDifferent e₁ e₂
      coord g n (← instantiateMVars e₁) e₂
    | n, e₁, e₂@(.mvar _) => do
      unless ← isDefEq e₁ e₂ do throwDifferent e₁ e₂
      coord g n e₁ (← instantiateMVars e₂)
    | _, _, _ => throwError "'Egg.Explanation.replaceSubexprs' tried to lens on different expressions or invalid coordinate"

  throwDifferent (e₁ e₂ : Expr) {α} : MetaM α :=
    throwError "Egg.Explanation.replaceSubexprs' tried to lens on different expressions:\n  {e₁}\nvs\n {e₂}"

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

abbrev AmbientMVars := PersistentHashMap MVarId MetavarDecl

def proof (expl : Explanation) (cgr : Congr) (rws : Rewrites) (amb : AmbientMVars) : MetaM Expr := do
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
    checkFinalProof proof current steps
    match cgr.rel with
    | .eq  => return proof
    | .iff => mkIffOfEq proof
where
  errorPrefix := "egg failed to reconstruct proof:"

  proofStep (current next : Expr) (rwInfo : Rewrite.Info) : MetaM Expr := do
    if rwInfo.src.isDefEq then return ← mkReflStep current next rwInfo.src
    let some rw := rws.find? rwInfo.src | throwError s!"{errorPrefix} unknown rewrite"
    if ← isRflProof rw.proof then return ← mkReflStep current next rwInfo.src
    mkCongrStep current next rwInfo.pos (← rw.forDir rwInfo.dir)

  mkReflStep (current next : Expr) (src : Source) : MetaM Expr := do
    unless ← isDefEq current next do
      throwError s!"{errorPrefix} unification failure for proof by reflexivity with rw {src.description}"
    mkEqRefl next

  mkCongrStep (current next : Expr) (pos : SubExpr.Pos) (rw : Rewrite) : MetaM Expr := do
    let mvc := (← getMCtx).mvarCounter
    let (lhs, rhs) ← placeCHoles current next pos rw
    try (← mkCongrOf 0 mvc lhs rhs).eq
    catch err => throwError m!"{errorPrefix} 'mkCongrOf' failed with\n  {err.toMessageData}"

  placeCHoles (current next : Expr) (pos : SubExpr.Pos) (rw : Rewrite) : MetaM (Expr × Expr) := do
    replaceSubexprs (root₁ := current) (root₂ := next) (p := pos) fun lhs rhs => do
      -- It's necessary that we create the fresh rewrite (that is, create the fresh mvars) in *this*
      -- local context as otherwise the mvars can't unify with variables under binders.
      let rw ← rw.fresh
      unless ← isDefEq lhs rw.lhs do throwError "{errorPrefix} unification failure for LHS of rewrite"
      unless ← isDefEq rhs rw.rhs do throwError "{errorPrefix} unification failure for RHS of rewrite"
      let proof ← rw.eqProof
      return (
        ← mkCHole (forLhs := true) lhs proof,
        ← mkCHole (forLhs := false) rhs proof
      )

  checkFinalProof (proof : Expr) (current : Expr) (steps : Array Step) : MetaM Unit := do
    let last := steps.back?.map (·.dst) |>.getD expl.start
    unless ← isDefEq current (← last.toExpr) do
      throwError s!"{errorPrefix} final expression is not defeq to rhs of proof goal"
    let proof ← instantiateMVars proof
    for mvar in (proof.collectMVars {}).result do
      unless amb.contains mvar do throwError s!"{errorPrefix} final proof contains mvar {mvar.name}"
