import Mathlib.Data.Finset.Lattice
import Mathlib.Tactic.PushNeg
import Egg

attribute [egg] Mathlib.Tactic.PushNeg.not_not_eq
attribute [egg] Mathlib.Tactic.PushNeg.not_and_eq
attribute [egg] Mathlib.Tactic.PushNeg.not_and_or_eq
attribute [egg] Mathlib.Tactic.PushNeg.not_or_eq
attribute [egg] Mathlib.Tactic.PushNeg.not_forall_eq
attribute [egg] Mathlib.Tactic.PushNeg.not_exists_eq
attribute [egg] Mathlib.Tactic.PushNeg.not_implies_eq
attribute [egg] Mathlib.Tactic.PushNeg.not_ne_eq
attribute [egg] Mathlib.Tactic.PushNeg.not_iff
attribute [egg] Mathlib.Tactic.PushNeg.not_nonempty_eq
attribute [egg] Mathlib.Tactic.PushNeg.ne_empty_eq_nonempty
attribute [egg] Mathlib.Tactic.PushNeg.empty_ne_eq_nonempty

section SemilatticeSup

variable [SemilatticeSup α] {a b c : α}

def SupIrred (a : α) : Prop :=
  ¬IsMin a ∧ ∀ ⦃b c⦄, b ⊔ c = a → b = a ∨ c = a

/-- A sup-prime element is a non-bottom element which isn't less than the supremum of anything
smaller. -/
def SupPrime (a : α) : Prop :=
  ¬IsMin a ∧ ∀ ⦃b c⦄, a ≤ b ⊔ c → a ≤ b ∨ a ≤ c

theorem SupIrred.not_isMin (ha : SupIrred a) : ¬IsMin a :=
  ha.1

theorem SupPrime.not_isMin (ha : SupPrime a) : ¬IsMin a :=
  ha.1

theorem IsMin.not_supIrred (ha : IsMin a) : ¬SupIrred a := fun h => h.1 ha

theorem IsMin.not_supPrime (ha : IsMin a) : ¬SupPrime a := fun h => h.1 ha


--set_option egg.timeLimit 10
set_option egg.reporting true
set_option trace.egg true

theorem not_supIrred : ¬SupIrred a ↔ IsMin a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  egg! [SupIrred, not_and_or, exists₂_congr, eq_comm]
  --rw [SupIrred, not_and_or]
  --push_neg
  --rw [exists₂_congr]
  --simp (config := { contextual := true }) [@eq_comm _ _ a]

theorem not_supPrime : ¬SupPrime a ↔ IsMin a ∨ ∃ b c, a ≤ b ⊔ c ∧ ¬a ≤ b ∧ ¬a ≤ c := by
--  egg! [SupPrime, not_and_or]
-- infinite loop?
  sorry

set_option egg.slotted true in

theorem not_supIrred' : ¬SupIrred a ↔ IsMin a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  egg! [SupIrred, not_and_or, exists₂_congr, eq_comm]
  --rw [SupIrred, not_and_or]
  --push_neg
  --rw [exists₂_congr]
  --simp (config := { contextual := true }) [@eq_comm _ _ a]

theorem not_supPrime' : ¬SupPrime a ↔ IsMin a ∨ ∃ b c, a ≤ b ⊔ c ∧ ¬a ≤ b ∧ ¬a ≤ c := by
 -- infinite loop?
  --egg! [SupPrime, not_and_or]
  sorry


end SemilatticeSup
