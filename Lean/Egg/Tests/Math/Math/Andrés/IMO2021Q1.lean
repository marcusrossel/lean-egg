import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Egg

open Finset

lemma exists_triplet_summing_to_squares {n : ℕ} (hn : 100 ≤ n) :
    ∃ a b c : ℕ, n ≤ a ∧ a < b ∧ b < c ∧ c ≤ 2 * n ∧
      IsSquare (a + b) ∧ IsSquare (c + a) ∧ IsSquare (b + c) := by
      sorry

attribute [egg neg] Mathlib.Tactic.PushNeg.not_not_eq
attribute [egg neg] Mathlib.Tactic.PushNeg.not_and_eq
attribute [egg neg] Mathlib.Tactic.PushNeg.not_and_or_eq
attribute [egg neg] Mathlib.Tactic.PushNeg.not_or_eq
attribute [egg neg] Mathlib.Tactic.PushNeg.not_forall_eq
attribute [egg neg] Mathlib.Tactic.PushNeg.not_exists_eq
attribute [egg neg] Mathlib.Tactic.PushNeg.not_implies_eq
attribute [egg neg] Mathlib.Tactic.PushNeg.not_ne_eq
attribute [egg neg] Mathlib.Tactic.PushNeg.not_iff
attribute [egg neg] Mathlib.Tactic.PushNeg.not_nonempty_eq
attribute [egg neg] Mathlib.Tactic.PushNeg.ne_empty_eq_nonempty
attribute [egg neg] Mathlib.Tactic.PushNeg.empty_ne_eq_nonempty

set_option egg.reporting true

theorem exists_finset_3_le_card_with_pairs_summing_to_squares {n : ℕ} (hn : 100 ≤ n) :
    ∃ B : Finset ℕ,
      2 * 1 + 1 ≤ #B ∧
      (∀ a ∈ B, ∀ b ∈ B, a ≠ b → IsSquare (a + b)) ∧
      ∀ c ∈ B, n ≤ c ∧ c ≤ 2 * n := by
  obtain ⟨a, b, c, hna, hab, hbc, hcn, h₁, h₂, h₃⟩ := exists_triplet_summing_to_squares hn
  refine ⟨{a, b, c}, ?_, ?_, ?_⟩
  · suffices a ∉ {b, c} ∧ b ∉ {c} by
    -- egg neg [Finset.card_insert_of_not_mem this.1, Finset.card_insert_of_not_mem this.2,
    --     Finset.card_singleton, Finset.mem_insert, Finset.mem_singleton, Finset.mem_singleton]
      rw [Finset.card_insert_of_not_mem this.1, Finset.card_insert_of_not_mem this.2,
        Finset.card_singleton]
    apply of_eq_true
    egg neg [Finset.mem_insert, Finset.mem_singleton, Finset.mem_singleton, hab, hbc, hbc]
    --rw [Finset.mem_insert, Finset.mem_singleton, Finset.mem_singleton]
    --push_neg
    --exact ⟨⟨hab.ne, (hab.trans hbc).ne⟩, hbc.ne⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with (rfl | rfl | rfl) <;> rcases hy with (rfl | rfl | rfl)
    all_goals
      first
      | contradiction
      | assumption
      | simpa only [add_comm x y]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro d (rfl | rfl | rfl) <;> constructor <;> linarith only [hna, hab, hbc, hcn]

set_option egg.slotted true
theorem exists_finset_3_le_card_with_pairs_summing_to_squares' {n : ℕ} (hn : 100 ≤ n) :
    ∃ B : Finset ℕ,
      2 * 1 + 1 ≤ #B ∧
      (∀ a ∈ B, ∀ b ∈ B, a ≠ b → IsSquare (a + b)) ∧
      ∀ c ∈ B, n ≤ c ∧ c ≤ 2 * n := by
  obtain ⟨a, b, c, hna, hab, hbc, hcn, h₁, h₂, h₃⟩ := exists_triplet_summing_to_squares hn
  refine ⟨{a, b, c}, ?_, ?_, ?_⟩
  · suffices a ∉ {b, c} ∧ b ∉ {c} by
    -- egg neg [Finset.card_insert_of_not_mem this.1, Finset.card_insert_of_not_mem this.2,
    --     Finset.card_singleton, Finset.mem_insert, Finset.mem_singleton, Finset.mem_singleton]
      rw [Finset.card_insert_of_not_mem this.1, Finset.card_insert_of_not_mem this.2,
        Finset.card_singleton]
    apply of_eq_true
    egg neg [Finset.mem_insert, Finset.mem_singleton, Finset.mem_singleton; hab, hbc, hbc]
    --push_neg
    --exact ⟨⟨hab.ne, (hab.trans hbc).ne⟩, hbc.ne⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with (rfl | rfl | rfl) <;> rcases hy with (rfl | rfl | rfl)
    all_goals
      first
      | contradiction
      | assumption
      | simpa only [add_comm x y]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro d (rfl | rfl | rfl) <;> constructor <;> linarith only [hna, hab, hbc, hcn]
