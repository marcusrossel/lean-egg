import Egg.Core.Explanation.Basic
import Egg.Core.Explanation.Congr
import Egg.Core.Explanation.Parse
import Egg.Core.Premise.Rewrites
import Egg.Core.Premise.Facts
import Egg.Core.Request.Equiv
open Lean Meta

namespace Egg.Explanation

private partial def replaceSubexprs
    (replace : (sub₁ sub₂ : Expr) → MetaM (Expr × Expr × ζ)) (p : SubExpr.Pos) (root₁ root₂ : Expr) :
    MetaM (Expr × Expr × ζ) :=
  go replace p.toArray.toList root₁ root₂
where
  go (g : Expr → Expr → MetaM (Expr × Expr × ζ)) : List Nat → Expr → Expr → MetaM (Expr × Expr × ζ)
    | [],       e₁, e₂ => g e₁ e₂
    | hd :: tl, e₁, e₂ => coord (go g tl) hd e₁ e₂

  coord (g : Expr → Expr → MetaM (Expr × Expr × ζ)) (c : Nat) (e₁ e₂ : Expr) : MetaM (Expr × Expr × ζ) := do
    match c, e₁, e₂ with
    | 0, .app f₁ a₁, .app f₂ a₂ => do
      unless ← isDefEq a₁ a₂ do throwDifferent e₁ e₂
      let (f₁', f₂', z) ← g f₁ f₂
      return (.app f₁' a₁, .app f₂' a₂, z)
    | 1, .app f₁ a₁, .app f₂ a₂ => do
      unless ← isDefEq f₁ f₂ do throwDifferent e₁ e₂
      let (a₁', a₂', z) ← g a₁ a₂
      return (.app f₁ a₁', .app f₂ a₂', z)
    | 0, .lam n₁ t₁ b₁ i₁, .lam n₂ t₂ b₂ i₂ => do
      unless ← isDefEq b₁ b₂ do throwDifferent e₁ e₂
      let (t₁', t₂', z) ← g t₁ t₂
      return (.lam n₁ t₁' b₁ i₁, .lam n₂ t₂' b₂ i₂, z)
    | 1, .lam n₁ t₁ b₁ i₁, .lam _ t₂ b₂ _ => do
      unless ← isDefEq t₁ t₂ do throwDifferent e₁ e₂
      withLocalDecl n₁ i₁ t₁ fun fvar => do
        let (b₁', b₂', z) ← g (b₁.instantiateRev #[fvar]) (b₂.instantiateRev #[fvar])
        return (← mkLambdaFVars #[fvar] b₁', ← mkLambdaFVars #[fvar] b₂', z)
    | 0, .forallE n₁ t₁ b₁ i₁, .forallE n₂ t₂ b₂ i₂ => do
      unless ← isDefEq b₁ b₂ do throwDifferent e₁ e₂
      let (t₁', t₂', z) ← g t₁ t₂
      return (.forallE n₁ t₁' b₁ i₁, .forallE n₂ t₂' b₂ i₂, z)
    | 1, .forallE n₁ t₁ b₁ i₁, .forallE _ t₂ b₂ _ => do
      unless ← isDefEq t₁ t₂ do throwDifferent e₁ e₂
      withLocalDecl n₁ i₁ t₁ fun fvar => do
        let (b₁', b₂', z) ← g (b₁.instantiateRev #[fvar]) (b₂.instantiateRev #[fvar])
        return (← mkForallFVars #[fvar] b₁', ← mkForallFVars #[fvar] b₂', z)
    | 0, .letE n₁ t₁ v₁ b₁ f₁, .letE n₂ t₂ v₂ b₂ f₂ => do
      unless ← isDefEq v₁ v₂ <&&> isDefEq b₁ b₂ do throwDifferent e₁ e₂
      let (t₁', t₂', z) ← g t₁ t₂
      return (.letE n₁ t₁' v₁ b₁ f₁, .letE n₂ t₂' v₂ b₂ f₂, z)
    | 1, .letE n₁ t₁ v₁ b₁ f₁, .letE n₂ t₂ v₂ b₂ f₂ => do
      unless ← isDefEq t₁ t₂ <&&> isDefEq b₁ b₂ do throwDifferent e₁ e₂
      let (v₁', v₂', z) ← g v₁ v₂
      return (.letE n₁ t₁ v₁' b₁ f₁, .letE n₂ t₂ v₂' b₂ f₂, z)
    | 2, .letE n₁ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ => do
      unless ← isDefEq t₁ t₂ <&&> isDefEq v₁ v₂ do throwDifferent e₁ e₂
      withLetDecl n₁ t₁ v₁ fun fvar => do
        let (b₁', b₂', z) ← g (b₁.instantiateRev #[fvar]) (b₂.instantiateRev #[fvar])
        return (← mkLetFVars #[fvar] b₁', ← mkLetFVars #[fvar] b₂', z)
    | 0, .proj t₁ i₁ s₁, .proj t₂ i₂ s₂ => do
      unless t₁ == t₂ && i₁ == i₂ do throwDifferent e₁ e₂
      let (s₁', s₂', z) ← g s₁ s₂
      return (.proj t₁ i₁ s₁', .proj t₂ i₂ s₂', z)
    | n, .mdata d₁ e₁, .mdata d₂ e₂ => do
      let (e₁', e₂', z) ← coord g n e₁ e₂
      return (.mdata d₁ e₁', .mdata d₂ e₂', z)
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
  | proof prop      => do mkFreshExprMVar (← toExpr prop)
  | subst idx to e  => return applySubst idx (← to.toExpr) (← e.toExpr)
  | shift off cut e => return applyShift off cut (← e.toExpr)
where
  applySubst (idx : Nat) (to : Expr) : Expr → Expr
    | .bvar i          => if i = idx then to else .bvar i
    | .app fn arg      => .app (applySubst idx to fn) (applySubst idx to arg)
    -- We don't shift `to` here because that's already handled in the egg backend. That is, the
    -- given `Expression` should contain the required shifts explicitly.
    | .lam n d b i     => .lam n (applySubst idx to d) (applySubst (idx + 1) to b) i
    | .forallE n d b i => .forallE n (applySubst idx to d) (applySubst (idx + 1) to b) i
    | e                => e
  applyShift (off : Int) (cut : Nat) : Expr → Expr
    | .bvar idx        => if idx < cut then .bvar idx else .bvar (idx + off).toNat
    | .app fn arg      => .app (applyShift off cut fn) (applyShift off cut arg)
    | .lam n d b i     => .lam n (applyShift off cut d) (applyShift off (cut + 1) b) i
    | .forallE n d b i => .forallE n (applyShift off cut d) (applyShift off (cut + 1) b) i
    | e                => e

end Explanation

namespace Proof

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
    let (prf, sub) ← proofStep current next step.toInfo
    steps    := steps.push prf
    subgoals := subgoals ++ sub
    current  := next
  return { steps, subgoals }
where
  fail {α} (msg : MessageData) : MetaM α := do
    throwError m!"egg failed to build proof: {msg}"

  proofStep (current next : Expr) (rwInfo : Rewrite.Info) : MetaM (Proof.Step × Proof.Subgoals) := do
    if rwInfo.src.isDefEq then
      let step := {
        lhs := current, rhs := next, proof := ← mkReflStep current next rwInfo.toDescriptor,
        rw := .defeq rwInfo.src, dir := rwInfo.dir
      }
      return (step, [])
    let some rw := rws.find? rwInfo.src | fail s!"unknown rewrite {rwInfo.src.description}"
    -- TODO: Can there be conditional rfl proofs?
    if ← isRflProof rw.proof then
      let step := {
        lhs := current, rhs := next, proof := ← mkReflStep current next rwInfo.toDescriptor,
        rw := .rw rw (isRefl := true), dir := rwInfo.dir
      }
      return (step, [])
    let facts ← rwInfo.facts.mapM fun src? => do
      let some src := src? | pure none
      facts.find? (·.src == src) |>.getDM <| fail m!"explanation references unknown fact {src}"
    let (prf, subgoals) ← mkCongrStep current next rwInfo.pos?.get! (← rw.forDir rwInfo.dir) facts
    let step := {
      lhs := current, rhs := next, proof := prf,
      rw := .rw rw (isRefl := false), dir := rwInfo.dir
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
