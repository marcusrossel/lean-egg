import Egg

-- Tests for manually inspecting what terms look like with or without proof erasure.
set_option trace.egg true

example (i : Nat) (h : i < 10) : (Fin.mk i h).val = i := by
  have : ∀ n m (g : n < m), (Fin.mk n g).val = n := by simp
  egg (config := { eraseProofs := true }) [this]

example (i : Nat) (h : i < 10) : (Fin.mk i h).val = i := by
  have : ∀ n m (g : n < m), (Fin.mk n g).val = n := by simp
  egg (config := { eraseProofs := false }) [this]
