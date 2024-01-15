import Egg

-- TODO: Could we generalize `egg` to work with any congruence relation which is supported by `rw`?

example : True ↔ True := by
  egg

example (p q : Prop) (h : p ↔ q) : p ↔ q := by
  egg [h]

example (x : Nat) : (x.add (.succ .zero) = x) ↔ ((Nat.succ .zero).add x = x) := by
  have h (x y : Nat) : x.add y = y.add x := Nat.add_comm ..
  egg [h]
