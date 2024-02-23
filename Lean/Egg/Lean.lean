import Lean

def List.replicateM [Monad m] (count : Nat) (f : m α) : m (List α) := do
  let mut result := []
  for _ in [0:count] do
    result := result.concat (← f)
  return result

namespace Lean

-- Note: The `_uniq` prefix comes from the `NameGenerator`.

-- Note that loose fvars' names are pretty printed using the `_fvar` prefix, but the underlying name
-- still uses the `_uniq` prefix:
-- https://github.com/leanprover/lean4-nightly/blob/d569ed4e5f796bbabbe17302a7c5a7060a4c7de7/src/Lean/PrettyPrinter/Delaborator/Builtins.lean#L33
def FVarId.uniqueIdx! : FVarId → Nat
  | { name := .num (.str .anonymous "_uniq") idx } => idx
  | _ => panic! "tried to access unique index of non-unique fvar-id"

def FVarId.fromUniqueIdx (idx : Nat) : FVarId :=
  { name := .num (.str .anonymous "_uniq") idx }

def MVarId.uniqueIdx! : MVarId → Nat
  | { name := .num (.str .anonymous "_uniq") idx } => idx
  | _ => panic! "tried to access unique index of non-unique mvar-id"

def MVarId.fromUniqueIdx (idx : Nat) : MVarId :=
  { name := .num (.str .anonymous "_uniq") idx }

-- Note that level mvars' names are pretty printed using the `?u` prefix, but the underlying name
-- still uses the `_uniq` prefix:
-- https://github.com/leanprover/lean4/blob/e206e53f4e37ecd810b2de36b7544240d579c535/src/Lean/Level.lean#L436
def LMVarId.uniqueIdx! : LMVarId → Nat
  | { name := .num (.str .anonymous "_uniq") idx } => idx
  | _ => panic! "tried to access unique index of non-unique level mvar-id"

def LMVarId.fromUniqueIdx (idx : Nat) : LMVarId :=
  { name := .num (.str .anonymous "_uniq") idx }

deriving instance BEq, Hashable for SubExpr.Pos

def HashMap.insertIfNew [BEq α] [BEq β] [Hashable α] [Hashable β]
    (m : HashMap α β) (a : α) (b : β) : HashMap α β :=
  if m.contains a then m else m.insert a b

def RBTree.merge (t₁ t₂ : RBTree α cmp) : RBTree α cmp :=
  t₁.mergeBy (fun _ _ _ => .unit) t₂

def RBTree.filter (t : RBTree α cmp) (keep : α → Bool) : RBTree α cmp :=
  t.fold (init := t) fun res a => if keep a then res else res.erase a

def RBTree.subtract (t₁ t₂ : RBTree α cmp) : RBTree α cmp :=
  t₁.filter (!t₂.contains ·)

def RBTree.singleton (a : α) : RBTree α cmp :=
  insert ∅ a

open Meta in
def replaceSubexprs
    (replace : (sub₁ sub₂ : Expr) → MetaM (Expr × Expr)) (p : SubExpr.Pos) (root₁ root₂ : Expr) :
    MetaM (Expr × Expr) :=
  go replace p.toArray.toList root₁ root₂
where
  go (g : Expr → Expr → MetaM (Expr × Expr)) : List Nat → Expr → Expr → MetaM (Expr × Expr)
    | [],       e₁, e₂ => g e₁ e₂
    | hd :: tl, e₁, e₂ => coord (go g tl) hd e₁ e₂

  coord (g : Expr → Expr → MetaM (Expr × Expr)) : Nat → Expr → Expr → MetaM (Expr × Expr)
    | 0, .app f₁ a₁, .app f₂ a₂ => do
      unless a₁ == a₂ do throwDifferent
      let (f₁', f₂') ← g f₁ f₂
      return (.app f₁' a₁, .app f₂' a₂)
    | 1, .app f₁ a₁, .app f₂ a₂ => do
      unless f₁ == f₂ do throwDifferent
      let (a₁', a₂') ← g a₁ a₂
      return (.app f₁ a₁', .app f₂ a₂')
    | 0, .lam n₁ t₁ b₁ i₁, .lam n₂ t₂ b₂ i₂ => do
      unless b₁ == b₂ do throwDifferent
      let (t₁', t₂') ← g t₁ t₂
      return (.lam n₁ t₁' b₁ i₁, .lam n₂ t₂' b₂ i₂)
    | 1, .lam n₁ t₁ b₁ i₁, .lam _ t₂ b₂ _ => do
      unless t₁ == t₂ do throwDifferent
      withLocalDecl n₁ i₁ t₁ fun fvar => do
        let (b₁', b₂') ← g (b₁.instantiateRev #[fvar]) (b₂.instantiateRev #[fvar])
        return (← mkLambdaFVars #[fvar] b₁', ← mkLambdaFVars #[fvar] b₂')
    | 0, .forallE n₁ t₁ b₁ i₁, .forallE n₂ t₂ b₂ i₂ => do
      unless b₁ == b₂ do throwDifferent
      let (t₁', t₂') ← g t₁ t₂
      return (.forallE n₁ t₁' b₁ i₁, .forallE n₂ t₂' b₂ i₂)
    | 1, .forallE n₁ t₁ b₁ i₁, .forallE _ t₂ b₂ _ => do
      unless t₁ == t₂ do throwDifferent
      withLocalDecl n₁ i₁ t₁ fun fvar => do
        let (b₁', b₂') ← g (b₁.instantiateRev #[fvar]) (b₂.instantiateRev #[fvar])
        return (← mkForallFVars #[fvar] b₁', ← mkForallFVars #[fvar] b₂')
    | 0, .letE n₁ t₁ v₁ b₁ f₁, .letE n₂ t₂ v₂ b₂ f₂ => do
      unless v₁ == v₂ && b₁ == b₂ do throwDifferent
      let (t₁', t₂') ← g t₁ t₂
      return (.letE n₁ t₁' v₁ b₁ f₁, .letE n₂ t₂' v₂ b₂ f₂)
    | 1, .letE n₁ t₁ v₁ b₁ f₁, .letE n₂ t₂ v₂ b₂ f₂ => do
      unless t₁ == t₂ && b₁ == b₂ do throwError ""
      let (v₁', v₂') ← g v₁ v₂
      return (.letE n₁ t₁ v₁' b₁ f₁, .letE n₂ t₂ v₂' b₂ f₂)
    | 2, .letE n₁ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _ => do
      unless t₁ == t₂ && v₁ == v₂ do throwDifferent
      withLetDecl n₁ t₁ v₁ fun fvar => do
        let (b₁', b₂') ← g (b₁.instantiateRev #[fvar]) (b₂.instantiateRev #[fvar])
        return (← mkLetFVars #[fvar] b₁', ← mkLetFVars #[fvar] b₂')
    | 0, .proj t₁ i₁ s₁, .proj t₂ i₂ s₂ => do
      unless t₁ == t₂ && i₁ == i₂ do throwDifferent
      let (s₁', s₂') ← g s₁ s₂
      return (.proj t₁ i₁ s₁', .proj t₂ i₂ s₂')
    | n, .mdata d₁ e₁, .mdata d₂ e₂ => do
      let (e₁', e₂') ← coord g n e₁ e₂
      return (.mdata d₁ e₁', .mdata d₂ e₂')
    | 3, _, _ =>
      throwError "'Lean.replaceSubexprs' tried to lens on types (this is not supported)"
    | _, _, _ =>
      throwError "'Lean.replaceSubexprs' tried to lens on different expressions or invalid coordinate"

  throwDifferent {α} : MetaM α :=
    throwError "'Lean.replaceSubexprs' tried to lens on different expressions"
