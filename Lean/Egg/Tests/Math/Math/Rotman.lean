import Mathlib
import Egg

-- From Rotman
axiom proposition_1_14 (n r : Nat) : (n + 1).choose r = n.choose (r - 1) + n.choose r

notation:100 r "﹗" => Real.Gamma (r + 1)

open Nat

theorem proposition_1_15 {n r : Nat} (h : n ≥ r) : n.choose r = (n !) / (r ! * (n - r)!) := by
  induction n generalizing r
  case zero => rw [Nat.le_zero.mp h]; rfl
  case succ n hi =>
    by_cases hr : r = 0 <;> try subst hr
    all_goals try by_cases hn : r = n + 1 <;> try subst hn
    all_goals try simp; rw [Nat.div_self <| factorial_pos _]

    have fromReal : (n + 1)﹗ / (r﹗ * (n + 1 - r)﹗) = ↑((n + 1)! / (r ! * (n + 1 - r)!)) := by
      have h₁ : r ≤ n + 1                          := by omega
      have h₂ : (r ! * (n + 1 - r)!) ∣ (n + 1)!    := sorry
      have h₃ : ↑(r ! * (n + 1 - r)!) ≠ (0 : Real) := by rw [cast_ne_zero]; exact mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)
      egg [cast_one, cast_add, cast_sub, cast_mul, cast_div, Real.Gamma_nat_eq_factorial, h₁, h₂, h₃]

    have toReal : ↑((n !) / ((r - 1)! * (n - r + 1)!) + (n !) / (r ! * (n - r)!)) = (n﹗ / ((r - 1)﹗ * (n - r + 1)﹗) + n﹗ / (r ﹗ * (n - r)﹗)) := by
      have h₁ : 1 ≤ r                                   := by omega
      have h₂ : r ≤ n                                   := by omega
      have h₃ : (r ! * (n - r)!) ∣ (n !)                := sorry
      have h₄ : ↑(r ! * (n - r)!) ≠ (0 : Real)          := by rw [cast_ne_zero]; exact mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)
      have h₅ : ((r - 1)! * (n - r + 1)!) ∣ (n !)       := sorry
      have h₆ : ↑((r - 1)! * (n - r + 1)!) ≠ (0 : Real) := by rw [cast_ne_zero]; exact mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)
      egg [cast_one, cast_add, cast_mul, cast_sub, cast_div, Real.Gamma_nat_eq_factorial, h₁, h₂, h₃, h₄, h₅, h₆]

    have h₁ : n ≥ r - 1               := by omega
    have h₂ : n ≥ r                   := by omega
    have h₃ : n - (r - 1) = n - r + 1 := by omega
    have h₄ : (n : Real) - r + 1 ≠ 0  := by rw [←cast_one, ←cast_sub h₂, ←cast_add, cast_ne_zero]; omega
    have h₅ : (r : Real) ≠ 0          := by rw [cast_ne_zero, ne_eq]; exact hr
    have h₆ : (n : Real) + 1 ≠ 0      := by rw [←cast_one, ←cast_add, cast_ne_zero]; omega

    calc (n + 1).choose r
      _ = (n !) / ((r - 1)! * (n - r + 1)!) + (n !) / (r ! * (n - r)!) := by egg [proposition_1_14, hi, h₁, h₂, h₃]
      _ = _ := Nat.cast_inj.mp <| by
        egg calc [toReal, fromReal, add_comm, sub_add_cancel, sub_add_eq_add_sub, mul_one, mul_comm,
                  mul_assoc, mul_div_mul_left, _root_.div_mul_div_comm, _root_.add_div,
                  div_mul_eq_div_mul_one_div, left_distrib, Real.Gamma_add_one, h₄, h₅, h₆]
          ↑((n !) / ((r - 1)! * (n - r + 1)!) + (n !) / (r ! * (n - r)!))
          _ = (n﹗ / ((r - 1)﹗ * (n - r + 1)﹗) + n﹗ / (r ﹗ * (n - r)﹗))
          _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * (1 / (n - r + 1) + 1 / r)
          _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * ((r + (n - r + 1)) / (r * (n - r + 1)))
          _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * ((n + 1) / (r * (n - r + 1)))
          _ = (n + 1)﹗ / (r﹗ * (n + 1 - r)﹗)
          _ = ↑((n + 1)! / (r ! * (n + 1 - r)!))
