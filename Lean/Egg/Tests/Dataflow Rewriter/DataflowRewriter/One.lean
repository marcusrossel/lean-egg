import Egg
import Mathlib

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
        (@Fin.val_lt_of_le (@List.length T x1) (@List.length T (@Prod.mk (List T) (List T) x1 x2).1)
          (@Fin.mk (@List.length T (@Prod.mk (List T) (List T) x1 x2).1) val isLt)
          (@le_refl Nat
            (@PartialOrder.toPreorder Nat (@StrictOrderedSemiring.toPartialOrder Nat Nat.instStrictOrderedSemiring))
            (@List.length T x1)))))
    (@List.get T x1 (@Fin.mk (@List.length T (@Prod.mk (List T) (List T) x1 x2).1) val isLt)) := by rfl

-- fails
example T x1 x2 val isLt :
  @Eq T
    (@List.get T x1
      (@Fin.mk (@List.length T x1) val
        (@Fin.val_lt_of_le (@List.length T x1) (@List.length T (@Prod.mk (List T) (List T) x1 x2).1)
          (@Fin.mk (@List.length T (@Prod.mk (List T) (List T) x1 x2).1) val isLt)
          (@le_refl Nat
            (@PartialOrder.toPreorder Nat (@StrictOrderedSemiring.toPartialOrder Nat Nat.instStrictOrderedSemiring))
            (@List.length T x1)))))
    (@List.get T x1 (@Fin.mk (@List.length T (@Prod.mk (List T) (List T) x1 x2).1) val isLt)) := by egg
