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
