import Egg

variable (h : ∀ x : Prop, (x ∧ x) = True)

example : True = (True ∧ True) := by
  refine Eq.trans (b := ?b ∧ ?b) ?eq₁ ?eq₂
  case eq₁ => egg [h]
  case eq₂ => exact rfl
