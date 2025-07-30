import Egg

def Mul.pow [Mul α] [One α] (a : α) : Nat → α
  | 0     => 1
  | n + 1 => a * (pow a n)

instance mulPow [Mul α] [One α] : Pow α Nat where
  pow := Mul.pow

example [Mul α] [One α] (a : α) : Mul.pow a 0 = (1 : α) := by
  egg [Mul.pow]

-- Note: This relies on generated type class projection reductions.
example [Mul α] [One α] (a : α) : a ^ 0 = (1 : α) := by
  egg [Mul.pow]
