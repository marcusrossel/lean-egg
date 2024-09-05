import Egg

-- This used to get stuck due to missing bvar e-class analyses for the subst and shift constructs.

variable (h : ∀ {α β} {f : α → List β} {b} {l : List α}, b ∈ l.bind f ↔ ∃ a, a ∈ l ∧ b ∈ f a)

/-- error: egg failed to prove the goal (reached time limit) -/
#guard_msgs in
example {xs : List α} {ys : List β} : xy ∈ (xs.bind fun a => ys.map (Prod.mk a)) ↔ True := by
  egg [h]
