import Egg

attribute [egg add] Nat.add_comm Nat.add_assoc Nat.zero_add

example : 0 + a + b + c = c + b + a := by
  egg add

example (h : a = b) : 0 + a + b + c = c + a + a := by
  egg add [h]
