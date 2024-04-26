import Egg

example (h₁ : x ∧ y) (h₂ : x ∧ y → 1 = 2) : 1 = 2 := by
  egg [h₁, h₂]

example (h₁ : x ∧ y) (h₂ : x ∧ y → 1 = 2) : 1 = 2 := by
  egg [*]

example (h₁ : ∀ n, n > 2 → n = x) (h₂ : 3 > 2) : 3 = x := by
  egg [h₁, h₂]

-- This tests that we can handle multiple conditions.
example (h₁ : ∀ n, n > 2 → n > 3 → n = x) (h₂ : 4 > 2) (h₃ : 4 > 3) : 4 = x := by
  egg [h₁, h₂, h₃]

-- This tests that conditions and facts do not need to be in order for proof reconstruction to work.
example (h₁ : ∀ n, n > 2 → n > 3 → n = x) (h₃ : 4 > 3) (h₂ : 4 > 2) : 4 = x := by
  egg [h₁, h₂, h₃]

example {a : Nat} (h : a < b) : a % b = a := by
  egg [Nat.mod_eq_of_lt, h]

-- TODO: Add all rewrites to the set of facts.
example {x : Nat} (h₁ : x = y) (h₂ : x = y → 1 = 2) : 1 = 2 := by
  sorry -- egg [h₁, h₂]

/-- error: egg does not currently support rewrites with unbound conditions (level) -/
#guard_msgs in
example (h₁ : x = y) (h₂ : x = y → 1 = 2) : 1 = 2 := by
  egg [h₁, h₂]

/-- error: egg does not currently support rewrites with unbound conditions (expression) -/
#guard_msgs in
example (h₁ : Prop) (h₂ : ∀ p : Prop, p → 1 = id 1) : 1 = id 1 := by
  egg [h₁, h₂]

/- TODO:

Example of a sensible theorem (rewrite) with an unbound condition:

theorem thm (n m : Nat) (h : n > m) : n > 0 := by
  induction n
  case zero => contradiction
  case succ => simp

We could still try a best effort approach which checks the set of facts for statements of the
form `n > ?m`.
-/
