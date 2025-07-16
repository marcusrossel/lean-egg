import Egg

set_option egg.subgoals true

#guard_msgs in
example (a : Nat) (h : True → a = b) : a = b := by
  egg [h]

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
#guard_msgs in
example (a : Nat) (p q : Prop) (h : p → q → a = b) : a = b := by
  egg [h]

/--
error: unsolved goals
h : ∀ (m : Nat), m = 0 → 1 = 2
⊢ Nat

h : ∀ (m : Nat), m = 0 → 1 = 2
⊢ ?m.1468 = 0
-/
#guard_msgs in
example (h : ∀ m, m = 0 → 1 = 2) : 1 = 2 := by
  egg [h]
