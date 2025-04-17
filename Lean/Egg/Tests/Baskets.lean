import Egg

attribute [egg add] Nat.add_comm Nat.add_assoc Nat.zero_add

attribute [egg add_comm]  Nat.add_comm
attribute [egg add_assoc] Nat.add_assoc
attribute [egg zero_add]  Nat.zero_add

example : 0 + a + b + c = c + b + a := by
  egg add

example (h : a = b) : 0 + a + b + c = c + a + a := by
  egg add [h]

example (h : a = b) : 0 + a + b + c = c + a + a := by
  egg add_comm add_assoc zero_add [h]
