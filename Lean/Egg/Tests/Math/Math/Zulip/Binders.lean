import Mathlib.Data.Set.Basic
import Egg

variable (s t : Set ℕ)
open Set

-- https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Is.20simp.20only.20a.20sequence.20of.20intelligent.20rewrites.3F/near/530885662

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  -- goal: ∀ x ∈ {a | a ∈ s ∧ a ∈ u}, x ∈ {a | a ∈ t ∧ a ∈ u}
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  egg [subset_def, inter_def, inter_def, mem_setOf]
