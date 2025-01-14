import Egg

example : 0 = 0 := by
  egg

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  egg [h₁, h₂]

open List in
example (as bs : List α) : reverse (as ++ bs) = (reverse bs) ++ (reverse as) := by
  induction as generalizing bs with
  | nil  => egg [reverse_nil, append_nil, List.append]
  | cons => egg [*, append_assoc, reverse_cons, List.append]

variable (a b c d : Int)

example : ((a * b) - (2 * c)) * d - (a * b) = (d - 1) * (a * b) - (2 * c * d) := by
  egg [Int.sub_mul, Int.sub_sub, Int.add_comm, Int.mul_comm, Int.one_mul]

example {p q r : Prop} (h₁ : p) (h₂ : p ↔ q) (h₃ : q → (p ↔ r)) : p ↔ r := by
  egg [h₁, h₂, h₃]
