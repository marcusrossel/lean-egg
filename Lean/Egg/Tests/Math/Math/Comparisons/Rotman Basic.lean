import Mathlib

open Nat

notation:100 r "﹗" => Real.Gamma (r + 1)

variable {n r : Nat} (h₁ : n + 1 ≥ r) (h₂ : r ≠ 0) (h₃ : r ≠ n + 1)

example : n ! / ((r - 1)! * (n - r + 1)!) + n ! / (r ! * (n - r)!) = (n + 1)! / (r ! * (n + 1 - r)!) :=
  have h₁ : (r - 1)! * (n - r + 1)! ∣ n ! := sorry
  have h₂ : ↑((r - 1)! * (n - r + 1)!) ≠ (0 : ℝ) := sorry
  have h₃ : r ! * (n - r)! ∣ n ! := sorry
  have h₄ : ↑(r ! * (n - r)!) ≠ (0 : ℝ) := sorry
  have h₅ : (n : ℝ) - r + 1 ≠ 0 := sorry
  have h₆ : (r : ℝ) - 1 + 1 ≠ 0 := sorry
  have h₇ : (r : ℝ) ≠ 0 := sorry
  have h₈ : (n : ℝ) + 1 ≠ 0 := sorry
  have h₉ : r ! * (n + 1 - r)! ∣ (n + 1)! := sorry
  have h₁₀ : ↑(r ! * (n + 1 - r)!) ≠ (0 : ℝ) := sorry

  cast_inj.mp <| calc
    _ = n﹗ / ((r - 1)﹗ * (n - r + 1)﹗) + n﹗ / (r﹗ * (n - r)﹗) := by
      rw [cast_add, cast_div h₁ h₂, cast_div h₃ h₄, cast_mul, cast_mul]
      repeat' rw [← Real.Gamma_nat_eq_factorial]
      rw [cast_sub (by omega), cast_add, cast_sub (by omega), cast_one]
    _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * (1 / (n - r + 1) + 1 / r) := by
      rw [Real.Gamma_add_one h₅, mul_comm (n - r + 1 : ℝ),
          ← mul_assoc, div_mul_eq_div_mul_one_div, ← sub_add_cancel ↑r (1 : ℝ),
          Real.Gamma_add_one h₆]
      ring_nf
    _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * ((r + (n - r + 1)) / (r * (n - r + 1))) := by
      rw [div_add_div _ _ h₅ h₇]; ring
    _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * ((n + 1) / (r * (n - r + 1))) := by ring
    _ = (n + 1)﹗ / (r﹗ * (n + 1 - r)﹗) := by
      rw [_root_.div_mul_div_comm, mul_comm, ← Real.Gamma_add_one h₈, mul_assoc,
          mul_comm ((n - r : ℝ)﹗), mul_assoc, ← mul_assoc, mul_comm ((r - 1 : ℝ)﹗),
          sub_add, sub_self, sub_zero, ← Real.Gamma_add_one h₇, ← Real.Gamma_add_one h₅]
      ring_nf
    _ = _ := by
      rw [cast_div h₉ h₁₀, cast_mul]
      repeat' rw [← Real.Gamma_nat_eq_factorial]
      rw [cast_add, cast_sub (by omega), cast_add, cast_one]
