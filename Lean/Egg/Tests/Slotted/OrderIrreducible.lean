import Egg

namespace PushNeg

variable (p q : Prop) {α : Sort _} {β : Type _} (s : α → Prop)

theorem _root_.not_iff : ¬(a ↔ b) ↔ (¬a ↔ b) := @Decidable.not_iff b a (Classical.propDecidable b)

@[simp low] theorem not_forall {p : α → Prop} : (¬∀ x, p x) ↔ ∃ x, ¬p x := @Decidable.not_forall α p (Classical.propDecidable (∃ a, ¬ p a)) (fun x => Classical.propDecidable (p x))
theorem not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b := @Decidable.not_and_iff_or_not_not  a b (Classical.propDecidable a)
theorem iff_iff_and_or_not_and_not : (a ↔ b) ↔ a ∧ b ∨ ¬a ∧ ¬b :=
  @Decidable.iff_iff_and_or_not_and_not a b (Classical.propDecidable b)
@[simp] theorem not_not : ¬¬a ↔ a := @Decidable.not_not a (Classical.propDecidable a)

end PushNeg

section SemilatticeSup

class SemilatticeSup (α : Type _) extends LE α, LT α where

  -- From sup
  sup : α → α → α

  -- From preorder
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

  -- From PartialOrder
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b
  /-- The supremum is an upper bound on the first argument -/
  protected le_sup_left : ∀ a b : α, a ≤ sup a b
  /-- The supremum is an upper bound on the second argument -/
  protected le_sup_right : ∀ a b : α, b ≤ sup a b
  /-- The supremum is the *least* upper bound -/
  protected sup_le : ∀ a b c : α, a ≤ c → b ≤ c → sup a b ≤ c
  /-- Least upper bound (`\lub` notation) -/

infixl:68 " ⊔ " => SemilatticeSup.sup

variable [SemilatticeSup α] {a b c : α}

def IsMin (a : α) : Prop :=
  ∀ ⦃b⦄, b ≤ a → a ≤ b

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

theorem sup_eq_left : a ⊔ b = a ↔ b ≤ a := sorry
  --le_antisymm_iff.trans <| by simp [le_rfl]

theorem sup_eq_right : a ⊔ b = b ↔ a ≤ b := sorry
  --le_antisymm_iff.trans <| by simp [le_rfl]

theorem left_lt_sup : a < a ⊔ b ↔ ¬b ≤ a := sorry
  --le_sup_left.lt_iff_ne.trans <| not_congr left_eq_sup

theorem right_lt_sup : b < a ⊔ b ↔ ¬a ≤ b := sorry
  -- le_sup_right.lt_iff_ne.trans <| not_congr right_eq_sup

-- Manual version: rw + simp
example : ¬SupIrred a ↔ IsMin a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  rw [SupIrred, PushNeg.not_and_or]
  rw [ PushNeg.not_not, PushNeg.not_forall]
  simp[ PushNeg.not_forall]
  rw [exists₂_congr]
  simp (config := { contextual := true }) only [@eq_comm _ _ a, ne_eq, and_congr_right_iff,
    sup_eq_left, sup_eq_right, left_lt_sup, right_lt_sup, implies_true]

-- Manual version: rw + simp
example : ¬SupIrred a ↔ IsMin a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  rw [SupIrred, PushNeg.not_and_or]
  rw [ PushNeg.not_not, PushNeg.not_forall]
  simp[ PushNeg.not_forall]
  rw [exists₂_congr]
  simp (config := { contextual := true }) only [@eq_comm _ _ a, ne_eq, and_congr_right_iff,
    sup_eq_left, sup_eq_right, left_lt_sup, right_lt_sup, implies_true]

-- Just simp won't work
example : ¬SupIrred a ↔ IsMin a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  simp (config := {contextual := true}) [SupIrred, PushNeg.not_and_or, exists₂_congr, eq_comm, @eq_comm _ _ a, ne_eq, and_congr_right_iff, sup_eq_left, sup_eq_right, left_lt_sup, right_lt_sup, implies_true]
  sorry

open PushNeg

set_option egg.slotted true in
set_option egg.reporting true in
theorem not_supPrime : ¬SupPrime a ↔ IsMin a ∨ ∃ b c, a ≤ b ⊔ c ∧ ¬a ≤ b ∧ ¬a ≤ c := by
  egg [not_not, not_and, not_and_or, not_or, not_imp, not_forall, not_exists, SupPrime]

/--
error: egg found an explanation exceeding the length limit (6391 vs 1000)
You can increase this limit using 'set_option egg.explLengthLimit <num>'.
-/
#guard_msgs in
set_option egg.slotted false in
set_option egg.unionSemantics false in
example : ¬SupPrime a ↔ IsMin a ∨ ∃ b c, a ≤ b ⊔ c ∧ ¬a ≤ b ∧ ¬a ≤ c := by
  egg [not_not, not_and, not_and_or, not_or, not_imp, not_forall, not_exists, SupPrime]

set_option egg.slotted true in
set_option egg.reporting true in
theorem not_supIrred : ¬SupIrred a ↔ IsMin a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  have h x y : x ⊔ y = a ∧ ¬x = a ∧ ¬y = a ↔ x ⊔ y = a ∧ x < a ∧ y < a := by
    simp +contextual [eq_comm (b := a), sup_eq_left, sup_eq_right, left_lt_sup, right_lt_sup]
  egg [not_not, not_and, not_and_or, not_or, not_imp, not_forall, not_exists, SupIrred, exists₂_congr h]

-- egg explodes
/-
egg failed to prove the goal (reached time limit) -
eqsat time: 1540330ms
-
iters:      67
nodes:      488401
classes:    235193
⊢ binders: false
-/
set_option egg.timeLimit 100 in
set_option egg.iterLimit 100 in
set_option egg.slotted false in
set_option egg.unionSemantics false in
set_option egg.reporting true in
example : ¬SupIrred a ↔ IsMin a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  have h x y : x ⊔ y = a ∧ ¬x = a ∧ ¬y = a ↔ x ⊔ y = a ∧ x < a ∧ y < a := by
    simp +contextual [eq_comm (b := a), sup_eq_left, sup_eq_right, left_lt_sup, right_lt_sup]
  egg [not_not, not_and, not_and_or, not_or, not_imp, not_forall, not_exists, SupIrred, exists₂_congr h]

end SemilatticeSup
