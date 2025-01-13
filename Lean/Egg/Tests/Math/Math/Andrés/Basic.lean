import Mathlib
import Egg
import Mathlib.Tactic.Ring
import Mathlib.Tactic.PushNeg

-- cast_smul_eq_nnqsmul
namespace NNRat

#print Nat.cast_smul_eq_nsmul

variable (R S : Type*) [DivisionSemiring R] [CharZero R] [Semiring S] [Module ℚ≥0 S]

#check Nat.cast_smul_eq_nsmul
example [Module R S] (q : ℚ≥0) (a : S) : (q : R) • a = q • a := by
  refine MulAction.injective₀ (G₀ := ℚ≥0) (Nat.cast_ne_zero.2 q.den_pos.ne') ?_
  egg [
    mul_smul, den_mul_eq_num, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, smul_assoc,
    nsmul_eq_mul q.den (α := R), cast_natCast, cast_mul, den_mul_eq_num, cast_natCast,
    Nat.cast_smul_eq_nsmul
  ]

set_option egg.slotted true in
example [Module R S] (q : ℚ≥0) (a : S) : (q : R) • a = q • a := by
  refine MulAction.injective₀ (G₀ := ℚ≥0) (Nat.cast_ne_zero.2 q.den_pos.ne') ?_
  egg [
    mul_smul, den_mul_eq_num, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, smul_assoc,
    nsmul_eq_mul q.den (α := R), cast_natCast, cast_mul, den_mul_eq_num, cast_natCast,
    Nat.cast_smul_eq_nsmul
  ]

end NNRat

-- mem_sInf
namespace Order.Ideal

open Function Set
variable {P : Type*} [SemilatticeSup P] [OrderBot P] {x : P} {S : Set (Ideal P)}

example : x ∈ sInf S ↔ ∀ s ∈ S, x ∈ s := by
  egg [SetLike.mem_coe, coe_sInf, mem_iInter₂]

set_option egg.slotted true in
example : x ∈ sInf S ↔ ∀ s ∈ S, x ∈ s := by
  egg [SetLike.mem_coe, coe_sInf, mem_iInter₂]

end Order.Ideal

-- not_modEq_iff_ne_add_zsmul
namespace AddCommGroup

variable {α : Type*} [AddCommGroup α] {p a a₁ a₂ b b₁ b₂ c : α} {n : ℕ} {z : ℤ}

example : ¬a ≡ b [PMOD p] ↔ ∀ z : ℤ, b ≠ a + z • p := by
  egg [modEq_iff_eq_add_zsmul, not_exists]

set_option egg.slotted true in
example : ¬a ≡ b [PMOD p] ↔ ∀ z : ℤ, b ≠ a + z • p := by
  egg [modEq_iff_eq_add_zsmul, not_exists]

end AddCommGroup

-- trans_eq_none
namespace PEquiv

open Mathlib.Tactic.PushNeg

example (f : α ≃. β) (g : β ≃. γ) (a : α) : f.trans g a = none ↔ ∀ b c, b ∉ f a ∨ c ∉ g b := by
  egg [
    Option.eq_none_iff_forall_not_mem, mem_trans, imp_iff_not_or.symm, forall_swap, not_exists_eq,
    not_and_eq
  ]

set_option egg.slotted true in
example (f : α ≃. β) (g : β ≃. γ) (a : α) : f.trans g a = none ↔ ∀ b c, b ∉ f a ∨ c ∉ g b := by
  egg [
    Option.eq_none_iff_forall_not_mem, mem_trans, imp_iff_not_or.symm, forall_swap, not_exists_eq,
    not_and_eq
  ]

end PEquiv

namespace Mathlib.Tactic.PushNeg

#check not_not_eq
example : ¬ ¬ p = p := by
exact Eq.mpr (id (Mathlib.Tactic.PushNeg.not_not_eq (p = p))) (Eq.refl p)

section SemilatticeSup

variable [SemilatticeSup α] {a b c : α}

attribute [egg] Mathlib.Tactic.PushNeg.not_not_eq
attribute [egg] Mathlib.Tactic.PushNeg.not_and_eq
attribute [egg] Mathlib.Tactic.PushNeg.not_and_or_eq
attribute [egg] Mathlib.Tactic.PushNeg.not_or_eq
attribute [egg] Mathlib.Tactic.PushNeg.not_forall_eq
attribute [egg] Mathlib.Tactic.PushNeg.not_exists_eq
attribute [egg] Mathlib.Tactic.PushNeg.not_implies_eq
attribute [egg] Mathlib.Tactic.PushNeg.not_ne_eq
attribute [egg] Mathlib.Tactic.PushNeg.not_iff

set_option egg.slotted true in
example : ¬SupIrred a ↔ IsMin a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  have  h : ∀ (a_1 b : α), a_1 ⊔ b = a ∧ ¬a_1 = a ∧ ¬b = a ↔ a_1 ⊔ b = a ∧ a_1 < a ∧ b < a  := by
    simp (config := { contextual := true }) [@eq_comm _ _ a, ne_eq, and_congr_right_iff, sup_eq_left, sup_eq_right, left_lt_sup, right_lt_sup, implies_true]
  egg! [SupIrred, exists₂_congr h]

set_option egg.slotted false in
example : ¬SupIrred a ↔ IsMin a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  have  h : ∀ (a_1 b : α), a_1 ⊔ b = a ∧ ¬a_1 = a ∧ ¬b = a ↔ a_1 ⊔ b = a ∧ a_1 < a ∧ b < a  := by
    simp (config := { contextual := true }) [@eq_comm _ _ a, ne_eq, and_congr_right_iff, sup_eq_left, sup_eq_right, left_lt_sup, right_lt_sup, implies_true]
  egg! [SupIrred, exists₂_congr h]

end SemilatticeSup
