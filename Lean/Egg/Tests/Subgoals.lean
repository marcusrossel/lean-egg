import Egg

set_option egg.conditionSubgoals true

/--
error: unsolved goals
b a : Nat
h : True → a = b
⊢ True
-/
-- #guard_msgs in
example (a : Nat) (h : True → a = b) : a = b := by
  sorry -- egg [h]

/--
error: unsolved goals
b a : Nat
p q : Prop
h : p → q → a = b
⊢ p

b a : Nat
p q : Prop
h : p → q → a = b
⊢ q
-/
-- #guard_msgs in
example (a : Nat) (p q : Prop) (h : p → q → a = b) : a = b := by
  sorry -- egg [h]

-- BUG: This is a result of not collecting ambient mvars correctly.
--      The mvar is the *type* of `p` and/or `q`.
example (a : Nat) (h : p → q → a = b) : a = b := by
  sorry -- egg [h]
