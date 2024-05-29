import Egg

example (f : Nat → Nat) (h₁ : a = b) (h₂ : b = c) : f a = f c := by
  egg [h₁, h₂] -- simp, rw

example : (λ a => a * 1) = (λ a => a) := by
  egg [Nat.mul_one] -- simp

example (a : α) (l : List α) : [a].append l = a :: l := by
  egg [List.append] -- simp

example (a : α) (l : List α) : [a] ++ l = a :: l := by
  egg [List.append] -- simp
