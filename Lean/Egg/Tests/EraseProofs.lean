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

-- BUG: The rewrite is actually bidirectional, but the proof is the only reference to the mvar for
--      `x` on the rhs.
variable (h : ∀ x : Nat, x = (Exists.intro x x.zero_le).choose)
example : True = True := by
  sorry -- egg [h]
