import Mathlib

open Nat

notation:100 r "﹗" => Real.Gamma (r + 1)

variable {n r : Nat} (h₁ : n + 1 ≥ r) (h₂ : r ≠ 0) (h₃ : r ≠ n + 1)

example : n ! / ((r - 1)! * (n - r + 1)!) + n ! / (r ! * (n - r)!) = (n + 1)! / (r ! * (n + 1 - r)!) :=
  cast_inj.mp <| calc
    _ = n﹗ / ((r - 1)﹗ * (n - r + 1)﹗) + n﹗ / (r﹗ * (n - r)﹗) := by
      rw [cast_add, cast_div sorry sorry, cast_div sorry sorry, cast_mul, cast_mul]
      repeat' rw [← Real.Gamma_nat_eq_factorial]
      rw [cast_sub sorry, cast_add, cast_sub sorry, cast_one]
    _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * (1 / (n - r + 1) + 1 / r) := by
      rw (occs := [3]) [Real.Gamma_add_one sorry]
      rw (occs := [2]) [mul_comm]
      rw [← mul_assoc]
      rw [div_mul_eq_div_mul_one_div]
      rw (occs := [4]) [← sub_add_cancel ↑r (1 : Real)]
      rw (occs := [5]) [Real.Gamma_add_one sorry]
      rw [sub_add_cancel, mul_assoc]
      rw (occs := [3]) [mul_comm]
      rw (occs := [2]) [div_mul_eq_div_mul_one_div]
      rw [left_distrib]
    _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * ((r + (n - r + 1)) / (r * (n - r + 1))) := by
      rw [div_add_div _ _ sorry sorry, mul_one, one_mul]
      rw (occs := [3]) [mul_comm]
    _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * ((n + 1) / (r * (n - r + 1))) := by
      rw [← add_assoc]
      rw (occs := [5]) [add_comm]
      rw (occs := [3]) [sub_add]
      rw [sub_self, sub_zero]
    _ = (n + 1)﹗ / (r﹗ * (n + 1 - r)﹗) := by
      rw [_root_.div_mul_div_comm, mul_comm, ← Real.Gamma_add_one sorry, mul_assoc]
      rw (occs := [2]) [mul_comm]
      rw [mul_assoc, ← mul_assoc]
      rw (occs := [2]) [mul_comm]
      rw [sub_add, sub_self, sub_zero, ← Real.Gamma_add_one sorry, ← Real.Gamma_add_one sorry]
      rw (occs := [5]) [add_comm]
      rw [← add_sub_assoc]
      rw (occs := [5]) [add_comm]
    _ = _ := by
      rw [cast_div sorry sorry, cast_mul]
      repeat' rw [← Real.Gamma_nat_eq_factorial]
      rw [cast_add, cast_sub sorry, cast_add, cast_one]

example : n ! / ((r - 1)! * (n - r + 1)!) + n ! / (r ! * (n - r)!) = (n + 1)! / (r ! * (n + 1 - r)!) :=
  cast_inj.mp <| calc
    _ = n﹗ / ((r - 1)﹗ * (n - r + 1)﹗) + n﹗ / (r﹗ * (n - r)﹗) := by
      rw [cast_add, cast_div sorry sorry, cast_div sorry sorry, cast_mul, cast_mul]
      repeat' rw [← Real.Gamma_nat_eq_factorial]
      rw [cast_sub sorry, cast_add, cast_sub sorry, cast_one]
    _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * (1 / (n - r + 1) + 1 / r) := by
      rw (occs := [3]) [Real.Gamma_add_one sorry]
      rw (occs := [2]) [mul_comm]
      rw [← mul_assoc]
      rw [div_mul_eq_div_mul_one_div]
      rw (occs := [4]) [← sub_add_cancel ↑r (1 : Real)]
      rw (occs := [5]) [Real.Gamma_add_one sorry]
      ring
    _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * ((r + (n - r + 1)) / (r * (n - r + 1))) := by
      rw [div_add_div _ _ sorry sorry]
      ring
    _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * ((n + 1) / (r * (n - r + 1))) := by
      ring
    _ = (n + 1)﹗ / (r﹗ * (n + 1 - r)﹗) := by
      rw [_root_.div_mul_div_comm, mul_comm, ← Real.Gamma_add_one sorry, mul_assoc]
      rw (occs := [2]) [mul_comm]
      rw [mul_assoc, ← mul_assoc]
      rw (occs := [2]) [mul_comm]
      rw [sub_add, sub_self, sub_zero, ← Real.Gamma_add_one sorry, ← Real.Gamma_add_one sorry]
      ring_nf
    _ = _ := by
      rw [cast_div sorry sorry, cast_mul]
      repeat' rw [← Real.Gamma_nat_eq_factorial]
      rw [cast_add, cast_sub sorry, cast_add, cast_one]
