import Egg

example : true = true := by
  egg

-- Checks that we try to introduce assumptions until the goal is an equality.
example : True → true = true := by
  egg

-- Checks that we try to introduce assumptions until the goal is an equality.
example : True → False → true = true := by
  egg

abbrev P := ∀ x y : Nat, x + y = x + y

-- Checks that we try to introduce assumptions until the goal is an equality.
example : P := by
  egg

-- Checks that we do not unfold semi-reducible (or higher) definitions.

set_option allowUnsafeReducibility true in attribute [semireducible] P

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
example : P := by
  egg

abbrev Q := ∀ x : Nat, x = nat_lit 0

-- Checks that we can "see through" definitions in rewrites where the body is an equality.
example (h : Q) : 1 = 0 := by
  egg [h]

abbrev R := true = false

-- Checks that we can "see through" definitions in rewrites where the body needs unfolding.
example (h : R) : true = false := by
  egg [h]

abbrev S := ∀ _ : 0 = 0, R

-- Checks that we can "see through" definitions in rewrites where the body is not an equality.
example (h : S) : R := by
  egg [h]
