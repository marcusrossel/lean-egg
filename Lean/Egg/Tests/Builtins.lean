import Egg

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
set_option egg.builtins false in
example : Nat.succ a = a + 1 := by
  egg

set_option egg.builtins true in
example : Nat.succ a = a + 1 := by
  egg

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
set_option egg.builtins false in
example (a : Nat) (h₁ : a < b → 1 = 2) (h₂ : b > a) : 1 = 2 := by
  egg [h₁, h₂]

set_option egg.builtins true in
example (a : Nat) (h₁ : a < b → 1 = 2) (h₂ : b > a) : 1 = 2 := by
  egg [h₁, h₂]

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
set_option egg.builtins false in
example (a : Nat) (h₁ : a ≤ b → 1 = 2) (h₂ : b ≥ a) : 1 = 2 := by
  egg [h₁, h₂]

set_option egg.builtins true in
example (a : Nat) (h₁ : a ≤ b → 1 = 2) (h₂ : b ≥ a) : 1 = 2 := by
  egg [h₁, h₂]
