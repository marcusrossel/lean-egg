import Egg.Core.Explanation.Basic
open Lean Meta

namespace Egg.Explanation

partial def replaceSubexprs
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
      unless ← (return a₁ == a₂) <||> isDefEq a₁ a₂ do throwDifferent e₁ e₂
      let (f₁', f₂', z) ← g f₁ f₂
      return (.app f₁' a₁, .app f₂' a₂, z)
    | 1, .app f₁ a₁, .app f₂ a₂ => do
      unless ← (return f₁ == f₂) <||> isDefEq f₁ f₂ do throwDifferent e₁ e₂
      let (a₁', a₂', z) ← g a₁ a₂
      return (.app f₁ a₁', .app f₂ a₂', z)
    | 0, .lam n₁ t₁ b₁ i₁, .lam n₂ t₂ b₂ i₂ => do
      unless ← (return b₁ == b₂) <||> isDefEq b₁ b₂ do throwDifferent e₁ e₂
      let (t₁', t₂', z) ← g t₁ t₂
      return (.lam n₁ t₁' b₁ i₁, .lam n₂ t₂' b₂ i₂, z)
    | 1, .lam n₁ t₁ b₁ i₁, .lam _ t₂ b₂ _ => do
      unless ← (return t₁ == t₂) <||> isDefEq t₁ t₂ do throwDifferent e₁ e₂
      withLocalDecl n₁ i₁ t₁ fun fvar => do
        let (b₁', b₂', z) ← g (b₁.instantiateRev #[fvar]) (b₂.instantiateRev #[fvar])
        return (← mkLambdaFVars #[fvar] b₁', ← mkLambdaFVars #[fvar] b₂', z)
    | 0, .forallE n₁ t₁ b₁ i₁, .forallE n₂ t₂ b₂ i₂ => do
      unless ← (return b₁ == b₂) <||> isDefEq b₁ b₂ do throwDifferent e₁ e₂
      let (t₁', t₂', z) ← g t₁ t₂
      return (.forallE n₁ t₁' b₁ i₁, .forallE n₂ t₂' b₂ i₂, z)
    | 1, .forallE n₁ t₁ b₁ i₁, .forallE _ t₂ b₂ _ => do
      unless ← (return t₁ == t₂) <||> isDefEq t₁ t₂ do throwDifferent e₁ e₂
      withLocalDecl n₁ i₁ t₁ fun fvar => do
        let (b₁', b₂', z) ← g (b₁.instantiateRev #[fvar]) (b₂.instantiateRev #[fvar])
        return (← mkForallFVars #[fvar] b₁', ← mkForallFVars #[fvar] b₂', z)
    | 0, .letE n₁ t₁ v₁ b₁ f₁, .letE n₂ t₂ v₂ b₂ f₂ => do
      unless ← ((return v₁ == v₂) <||> isDefEq v₁ v₂) <&&> ((return b₁ == b₂) <||> isDefEq b₁ b₂) do throwDifferent e₁ e₂
      let (t₁', t₂', z) ← g t₁ t₂
      return (.letE n₁ t₁' v₁ b₁ f₁, .letE n₂ t₂' v₂ b₂ f₂, z)
    | 1, .letE n₁ t₁ v₁ b₁ f₁, .letE n₂ t₂ v₂ b₂ f₂ => do
      unless ← ((return t₁ == t₂) <||> isDefEq t₁ t₂) <&&> ((return b₁ == b₂) <||> isDefEq b₁ b₂) do throwDifferent e₁ e₂
      let (v₁', v₂', z) ← g v₁ v₂
      return (.letE n₁ t₁ v₁' b₁ f₁, .letE n₂ t₂ v₂' b₂ f₂, z)
    | 2, .letE n₁ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ => do
      unless ← ((return t₁ == t₂) <||> isDefEq t₁ t₂) <&&> ((return v₁ == v₂) <||> isDefEq v₁ v₂) do throwDifferent e₁ e₂
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
