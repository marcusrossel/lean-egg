import Egg

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
set_option egg.genGroundEqs false in
example (h₁ : ∀ p, p ∧ p) (h₂ : (∀ p, p ∧ p) → q = True) : q = True := by
  egg [h₁, h₂]

set_option egg.genGroundEqs true in
example (h₁ : ∀ p, p ∧ p) (h₂ : (∀ p, p ∧ p) → q = True) : q = True := by
  egg [h₁, h₂]
