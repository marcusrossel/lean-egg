import Egg

-- Tests for manually inspecting what terms look like with or without proof erasure.

example (i : Nat) (h : i < 10) : (Fin.mk i h).val = i := by
  have : ∀ n m (g : n < m), (Fin.mk n g).val = n := by simp
  egg (config := { eraseProofs := false }) [this]

example (i : Nat) (h : i < 10) : (Fin.mk i h).val = i := by
  have : ∀ n m (g : n < m), (Fin.mk n g).val = n := by simp
  egg (config := { eraseProofs := true }) [this]

example (i : Nat) (h : ∀ i : Nat, i < 10) : (Fin.mk i (h i)).val = i := by
  have : ∀ n m (g : n < m), (Fin.mk n g).val = n := by simp
  egg (config := { eraseProofs := true }) [this]

-- TODO:
-- Mathlib's Function.factorsThrough_iff breaks when using proof erasure with error message
--  (kernel) declaration has metavariables 'Function.factorsThrough_iff'
-- So it seems to be a case where we don't manage to reconstruct all mvars.
