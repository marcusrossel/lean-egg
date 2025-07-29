import Egg

-- works
example {α} {l : List α} (i : Nat) (h₁ h₂ : i < l.length) :
  l.get (Fin.mk i h₁) = l.get (Fin.mk i h₂) := by rfl

-- works
example {α} {l : List α} (i : Nat) (h₁ h₂ : i < l.length) :
  Fin.mk i h₁ = Fin.mk i h₂ := by rfl

-- works
example {α} {l : List α} (i : Nat) (h₁ h₂ : i < l.length) :
  l.get (Fin.mk i h₁) = l.get (Fin.mk i h₂) := by egg

-- works
example {α} {l : List α} (i : Nat) (h₁ h₂ : i < l.length) :
  Fin.mk i h₁ = Fin.mk i h₂ := by egg

-- works
example T x1 x2 val isLt :
  @Eq T
    (@List.get T x1
      (@Fin.mk (@List.length T x1) val
        isLt))
    (@List.get T x1
      (@Fin.mk (@List.length T (@Prod.mk (List T) (List T) x1 x2).1) val
        isLt)) := by egg

-- proof irrelevance works
example (n val : Nat) (isLt₁ isLt₂ : val < n) :
  Eq (@Fin.mk n val isLt₁)
     (@Fin.mk n val isLt₂) := by egg

-- structure projection rfl works
example {val n isLt} : (@Fin.val n ⟨val, isLt⟩) = val := by egg

-- proof irrelevance with value inside structure projection works
example {val m n isLt} : ((@Fin.val n ⟨val, isLt⟩) < m) = (val < m) := by egg

example {val n} (isLt : val < n) :
  (@LT.lt Nat instLTNat (↑(Fin.mk val isLt)) n) = (val < n) := by egg

-- TODO: Turning around the goal to be `isLt' = isLt` fails during proof reconstruction in the sense
--       that it produces a proof term containing unassigned mvars. I don't understand why this
--       happens. Moreover, wrapping parts of the goal in `id` fixes the problem, even though the
--       exact same explanation is produced.
example {val n} (isLt : val < n) (isLt' : (@LT.lt Nat instLTNat (↑(Fin.mk val isLt)) n)) :
    isLt' = isLt := by
  egg [*]

example {val T x1} (isLt : val < x1.length) :
  Eq (@Fin.val_lt_of_le (@List.length T x1) (@List.length T x1) (@Fin.mk (@List.length T x1) val isLt) (Nat.le_refl x1.length))
    isLt := by
      egg [*, Fin.val_lt_of_le]
