 import Egg.Core.Explanation.Basic
import Egg.Core.Explanation.Congr
import Egg.Core.Premise.Rewrites
open Lean Meta

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

end Explanation

inductive Proof.Step.Rewrite where
  | rw    (rw : Egg.Rewrite) (isRefl : Bool)
  | defeq (src : Source)
  deriving Inhabited

def Proof.Step.Rewrite.isRefl : Rewrite → Bool
  | rw _ isRefl => isRefl
  | defeq _     => true

structure Proof.Step where
  lhs   : Expr
  rhs   : Expr
  proof : Expr
  rw    : Step.Rewrite
  dir   : Direction
  deriving Inhabited

abbrev Proof := Array Proof.Step

def Proof.prove (prf : Proof) (cgr : Congr) : MetaM Expr := do
  let some first := prf[0]? | return (← cgr.rel.mkRefl cgr.lhs)
  unless ← isDefEq first.lhs cgr.lhs do fail "initial expression is not defeq to lhs of proof goal"
  let mut proof := first.proof
  for step in prf[1:] do
    if !step.rw.isRefl then proof ← mkEqTrans proof step.proof
  unless ← isDefEq prf.back.rhs cgr.rhs do fail "final expression is not defeq to rhs of proof goal"
  match cgr.rel with
  | .eq  => return proof
  | .iff => mkIffOfEq proof
where
  fail (msg : String) : MetaM Unit := do
    throwError s!"egg failed to build proof: {msg}"

def Explanation.proof (expl : Explanation) (rws : Rewrites) : MetaM Proof := do
  let mut current ← expl.start.toExpr
  let mut proof : Proof := #[]
  for step in expl.steps do
    let next ← step.dst.toExpr
    proof := proof.push (← proofStep current next step.toInfo)
    current := next
  return proof
where
  fail {α} (msg : MessageData) : MetaM α := do
    throwError m!"egg failed to build proof: {msg}"

  proofStep (current next : Expr) (rwInfo : Rewrite.Info) : MetaM Proof.Step := do
    if rwInfo.src.isDefEq then return {
      lhs := current, rhs := next, proof := ← mkReflStep current next rwInfo.toDescriptor,
      rw := .defeq rwInfo.src, dir := rwInfo.dir
    }
    let some rw := rws.find? rwInfo.src | fail s!"unknown rewrite {rwInfo.src.description}"
    if ← isRflProof rw.proof then return {
      lhs := current, rhs := next, proof := ← mkReflStep current next rwInfo.toDescriptor,
      rw := .rw rw (isRefl := true), dir := rwInfo.dir
    }
    let prf ← mkCongrStep current next rwInfo.pos (← rw.forDir rwInfo.dir)
    return {
      lhs := current, rhs := next, proof := prf,
      rw := .rw rw (isRefl := false), dir := rwInfo.dir
    }

  mkReflStep (current next : Expr) (rw : Rewrite.Descriptor) : MetaM Expr := do
    unless ← isDefEq current next do
      fail s!"unification failure for proof by reflexivity with rw {rw.src.description}"
    mkEqRefl next

  mkCongrStep (current next : Expr) (pos : SubExpr.Pos) (rw : Rewrite) : MetaM Expr := do
    let mvc := (← getMCtx).mvarCounter
    let (lhs, rhs) ← placeCHoles current next pos rw
    try (← mkCongrOf 0 mvc lhs rhs).eq
    catch err => fail m!"'mkCongrOf' failed with\n  {err.toMessageData}"

  placeCHoles (current next : Expr) (pos : SubExpr.Pos) (rw : Rewrite) : MetaM (Expr × Expr) := do
    replaceSubexprs (root₁ := current) (root₂ := next) (p := pos) fun lhs rhs => do
      -- It's necessary that we create the fresh rewrite (that is, create the fresh mvars) in *this*
      -- local context as otherwise the mvars can't unify with variables under binders.
      let rw ← rw.fresh
      unless ← isDefEq lhs rw.lhs do fail m!"unification failure for LHS of rewrite {rw.src.description}"
      unless ← isDefEq rhs rw.rhs do fail m!"unification failure for RHS of rewrite {rw.src.description}"
      let proof ← rw.eqProof
      return (
        ← mkCHole (forLhs := true) lhs proof,
        ← mkCHole (forLhs := false) rhs proof
      )
