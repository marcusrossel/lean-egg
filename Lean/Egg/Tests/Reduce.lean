import Egg

example : true = true := by
  egg

-- Checks that we try to introduce assumptions until the goal is an equality.
example : True → true = true := by
  egg

-- Checks that we try to introduce assumptions until the goal is an equality.
example : True → False → true = true := by
  egg

def P := ∀ x y : Nat, x + y = x + y

-- Checks that we try to introduce assumptions until the goal is an equality.
example : P := by
  egg

def Q := ∀ x : Nat, x = 0

-- Checks that we can "see through" definitions in rewrites where the body is an equality.
example (h : Q) : 1 = 0 := by
  egg [h]

def R := true = false

-- Checks that we can "see through" definitions in rewrites where the body needs unfolding.
example (h : R) : true = false := by
  egg [h]

def S := ∀ _ : 0 = 0, R

-- Checks that we can "see through" definitions in rewrites where the body is not an equality.
example (h : S) : R := by
  egg [h]
