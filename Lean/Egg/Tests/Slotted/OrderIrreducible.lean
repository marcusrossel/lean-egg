import Egg

namespace PushNeg

variable (p q : Prop) {α : Sort _} {β : Type _} (s : α → Prop)

theorem _root_.not_iff : ¬(a ↔ b) ↔ (¬a ↔ b) := @Decidable.not_iff b a (Classical.propDecidable b)

@[simp low] theorem not_forall {p : α → Prop} : (¬∀ x, p x) ↔ ∃ x, ¬p x := @Decidable.not_forall α p (Classical.propDecidable (∃ a, ¬ p a)) (fun x => Classical.propDecidable (p x))
theorem not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b := @Decidable.not_and_iff_or_not_not  a b (Classical.propDecidable a)
theorem iff_iff_and_or_not_and_not : (a ↔ b) ↔ a ∧ b ∨ ¬a ∧ ¬b :=
  @Decidable.iff_iff_and_or_not_and_not a b (Classical.propDecidable b)
@[simp] theorem not_not : ¬¬a ↔ a := @Decidable.not_not a (Classical.propDecidable a)

@[egg] theorem not_not_eq : (¬ ¬ p) = p := propext Classical.not_not
@[egg] theorem not_and_eq : (¬ (p ∧ q)) = (p → ¬ q) := propext not_and
@[egg] theorem not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ ¬ q) := propext not_and_or
@[egg] theorem not_or_eq : (¬ (p ∨ q)) = (¬ p ∧ ¬ q) := propext not_or
@[egg] theorem not_forall_eq : (¬ ∀ x, s x) = (∃ x, ¬ s x) := propext not_forall
@[egg] theorem not_exists_eq : (¬ ∃ x, s x) = (∀ x, ¬ s x) := propext not_exists
@[egg] theorem not_implies_eq : (¬ (p → q)) = (p ∧ ¬ q) := propext Classical.not_imp
@[egg] theorem not_ne_eq (x y : α) : (¬ (x ≠ y)) = (x = y) := ne_eq x y ▸ not_not_eq _
@[egg] theorem not_iff : (¬ (p ↔ q)) = ((p ∧ ¬ q) ∨ (¬ p ∧ q)) := propext <|
  _root_.not_iff.trans <| iff_iff_and_or_not_and_not.trans <| by rw [not_not, or_comm]

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

--set_option egg.timeLimit 10
set_option egg.reporting true
set_option trace.egg true

-- Manual version: rw + simp
example : ¬SupIrred a ↔ IsMin a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  --egg! [SupIrred, not_and_or, exists₂_congr, eq_comm]
  rw [SupIrred, PushNeg.not_and_or]
  rw [ PushNeg.not_not_eq, PushNeg.not_forall_eq]
  simp[ PushNeg.not_forall_eq]
  rw [exists₂_congr]
  simp (config := { contextual := true }) only [@eq_comm _ _ a, ne_eq, and_congr_right_iff,
    sup_eq_left, sup_eq_right, left_lt_sup, right_lt_sup, implies_true]

-- Manual version: rw + simp
example : ¬SupIrred a ↔ IsMin a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  --egg! [SupIrred, not_and_or, exists₂_congr, eq_comm]
  rw [SupIrred, PushNeg.not_and_or]
  rw [ PushNeg.not_not_eq, PushNeg.not_forall_eq]
  simp[ PushNeg.not_forall_eq]
  rw [exists₂_congr]
  simp (config := { contextual := true }) only [@eq_comm _ _ a, ne_eq, and_congr_right_iff,
    sup_eq_left, sup_eq_right, left_lt_sup, right_lt_sup, implies_true]

-- Just simp won't work
example : ¬SupIrred a ↔ IsMin a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  simp (config := {contextual := true}) [SupIrred, PushNeg.not_and_or, exists₂_congr, eq_comm, @eq_comm _ _ a, ne_eq, and_congr_right_iff, sup_eq_left, sup_eq_right, left_lt_sup, right_lt_sup, implies_true]
  sorry



set_option egg.slotted true in
theorem not_supPrime : ¬SupPrime a ↔ IsMin a ∨ ∃ b c, a ≤ b ⊔ c ∧ ¬a ≤ b ∧ ¬a ≤ c := by
  egg! [SupPrime, PushNeg.not_and_or]

-- infinite loop
set_option egg.slotted false in
set_option egg.unionSemantics false in
example : ¬SupPrime a ↔ IsMin a ∨ ∃ b c, a ≤ b ⊔ c ∧ ¬a ≤ b ∧ ¬a ≤ c := by
  sorry -- egg! [SupPrime, PushNeg.not_and_or]

set_option egg.slotted true in
theorem not_supIrred : ¬SupIrred a ↔ IsMin a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  have h : ∀ (a_1 b : α), a_1 ⊔ b = a ∧ ¬a_1 = a ∧ ¬b = a ↔ a_1 ⊔ b = a ∧ a_1 < a ∧ b < a := by
    simp (config := { contextual := true }) [@eq_comm _ _ a, ne_eq, and_congr_right_iff, sup_eq_left, sup_eq_right, left_lt_sup, right_lt_sup, implies_true]
  egg! [SupIrred, exists₂_congr h]

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
set_option egg.timeLimit 60 in
set_option egg.iterLimit 100 in
set_option egg.slotted false in
set_option egg.unionSemantics false in
example : ¬SupIrred a ↔ IsMin a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  have h : ∀ (a_1 b : α), a_1 ⊔ b = a ∧ ¬a_1 = a ∧ ¬b = a ↔ a_1 ⊔ b = a ∧ a_1 < a ∧ b < a := by
    simp (config := { contextual := true }) [@eq_comm _ _ a, ne_eq, and_congr_right_iff, sup_eq_left, sup_eq_right, left_lt_sup, right_lt_sup, implies_true]
  egg! [SupIrred, exists₂_congr h]

end SemilatticeSup
