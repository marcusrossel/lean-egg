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
@[egg] theorem not_iff : (¬ (p ↔ q)) = ((p ∧ ¬ q) ∨ (¬ p ∧ q)) := propext <| _root_.not_iff.trans <|
  iff_iff_and_or_not_and_not.trans <| by rw [not_not, or_comm]

-- TODO: This crashes because the explicit equality constructor erases certain mvars, which we still
--       need to account for during mvar collection.
example : ((fun x => x+x) 1) = 2 := by
  egg!

-- These should all work nicely with `simp_egg` in the future
/--
error: expected goal to be of type '=', '↔', '∀ ..., _ = _', or '∀ ..., _ ↔ _', but found:

  False
-/
#guard_msgs in
example : ¬ ¬ p = p := by
  egg!

example : (¬ ¬ p) = p := by
  egg!


/--
error: expected goal to be of type '=', '↔', '∀ ..., _ = _', or '∀ ..., _ ↔ _', but found:

  False
-/
#guard_msgs in
example : (¬p ∧ ¬q) → ¬(p ∨ q) := by
  intro h
  egg!
  exact h

/--
error: expected goal to be of type '=', '↔', '∀ ..., _ = _', or '∀ ..., _ ↔ _', but found:

  False
-/
#guard_msgs in
example : ¬(p ∧ q) → (p → ¬q) := by
  intro h
  egg!

/--
error: expected goal to be of type '=', '↔', '∀ ..., _ = _', or '∀ ..., _ ↔ _', but found:

  False
-/
#guard_msgs in
example {p' : α → Prop} : (∀(x : α), ¬ p' x) → ¬ ∃(x : α), p' x := by
  intro h
  egg!
