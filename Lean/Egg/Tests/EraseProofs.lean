import Egg

-- Tests for manually inspecting what terms look like with or without proof erasure.

set_option egg.eraseProofs true

set_option egg.eraseProofs false in
example (i : Nat) (h : i < 10) : (Fin.mk i h).val = i := by
  have : ∀ n m (g : n < m), (Fin.mk n g).val = n := by simp
  egg [this]

example (i : Nat) (h : i < 10) : (Fin.mk i h).val = i := by
  have : ∀ n m (g : n < m), (Fin.mk n g).val = n := by simp
  egg [this]

example (i : Nat) (h : ∀ i : Nat, i < 10) : (Fin.mk i (h i)).val = i := by
  have : ∀ n m (g : n < m), (Fin.mk n g).val = n := by simp
  egg [this]

-- BUG:
example
    (f : (a b : Nat) → a > b → Nat) (g : Nat → Nat) (a₁ a₂ b₁ b₂ c d : Nat) (h₁ : a₁ > b₁)
    (h₂ : a₂ > b₂) (h₃ : a₁ = c) (h₄ : a₂ = c) (h₅ : b₁ = d) (h₆ : d = b₂) :
    g (g (f a₁ b₁ h₁)) = g (g (f a₂ b₂ h₂)) := by
  sorry -- egg [*]

-- BUG: The rewrite is actually bidirectional, but the proof is the only reference to the mvar for
--      `x` on the rhs.
variable (h : ∀ x : Nat, x = (Exists.intro x x.zero_le).choose)
example : True = True := by
  sorry -- egg [h]
