import Egg

variable (a b c d : Int)

example : ((a * b) - (2 * c)) * d - (a * b) = (d - 1) * (a * b) - (2 * c * d) :=
  calc ((a * b) - (2 * c)) * d - (a * b)
    _ = (a * b * d) - (2 * c * d) - (a * b)     := by rw [Int.sub_mul]
    _ = (a * b * d) - (2 * c * d + a * b)       := by rw [Int.sub_sub]
    _ = (a * b * d) - (a * b + 2 * c * d)       := by rw [Int.add_comm]
    _ = (a * b * d) - (a * b) - (2 * c * d)     := by rw [Int.sub_sub]
    _ = (a * b * d) - 1 * (a * b) - (2 * c * d) := by rw [Int.one_mul]
    _ = d * (a * b) - 1 * (a * b) - (2 * c * d) := by rw [Int.mul_comm]
    _ = (d - 1) * (a * b) - (2 * c * d)         := by rw [Int.sub_mul]

example : ((a * b) - (2 * c)) * d - (a * b) = (d - 1) * (a * b) - (2 * c * d) := by
  egg calc [Int.sub_mul, Int.sub_sub, Int.add_comm, Int.mul_comm, Int.one_mul]
    ((a * b) - (2 * c)) * d - (a * b)
    _ = (a * b * d) - (2 * c * d) - (a * b)
    _ = (a * b * d) - (2 * c * d + a * b)
    _ = (a * b * d) - (a * b + 2 * c * d)
    _ = (a * b * d) - (a * b) - (2 * c * d)
    _ = (a * b * d) - 1 * (a * b) - (2 * c * d)
    _ = d * (a * b) - 1 * (a * b) - (2 * c * d)
    _ = (d - 1) * (a * b) - (2 * c * d)

example : ((a * b) - (2 * c)) * d - (a * b) = (d - 1) * (a * b) - (2 * c * d) := by
  egg calc [Int.sub_mul, Int.sub_sub, Int.add_comm, Int.mul_comm, Int.one_mul]
    ((a * b) - (2 * c)) * d - (a * b)
    _ = (a * b * d) - (2 * c * d) - (a * b)
    _ = (a * b * d) - (a * b) - (2 * c * d)
    _ = (a * b * d) - 1 * (a * b) - (2 * c * d)
    _ = (d - 1) * (a * b) - (2 * c * d)

example : ((a * b) - (2 * c)) * d - (a * b) = (d - 1) * (a * b) - (2 * c * d) := by
  egg [Int.sub_mul, Int.sub_sub, Int.add_comm, Int.mul_comm, Int.one_mul]

macro "int_arith" : tactic => `(tactic|
  egg [Int.sub_mul, Int.sub_sub, Int.add_comm, Int.mul_comm, Int.one_mul]
)

example : ((a * b) - (2 * c)) * d - (a * b) = (d - 1) * (a * b) - (2 * c * d) := by
  int_arith
