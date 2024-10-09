import Egg

-- These tests check that we don't override existing fvars' names with automatically introduced
-- names.

set_option linter.unusedVariables false

/--
info: Try this: ⏎
  intro x_1
  calc
    x_1
    _ = x_1 := Eq.refl x_1
-/
#guard_msgs in
example : Nat → (x : Nat) → x = x := by
  intro x
  egg?

/--
info: Try this: ⏎
  intro x x_1_1
  calc
    x
    _ = x := Eq.refl x
-/
#guard_msgs in
example : Nat → (x : Nat) → (x_1 : Nat) → x = x := by
  intro x_1
  egg?
