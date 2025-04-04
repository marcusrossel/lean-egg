import Mathlib
import Egg

open Nat

attribute [egg cast] cast_zero cast_one cast_two cast_three cast_four cast_succ cast_pred
                     cast_add_one cast_add cast_sub cast_mul cast_div cast_pow cast_dvd_cast cast_id
                     cast_ite

attribute [egg real] add_comm sub_add_cancel sub_add_eq_add_sub mul_one mul_comm mul_assoc
                     mul_div_mul_left _root_.div_mul_div_comm _root_.add_div
                     div_mul_eq_div_mul_one_div left_distrib

set_option egg.conditionSubgoals true

-- From Rotman
axiom proposition_1_14 (n r : Nat) : (n + 1).choose r = n.choose (r - 1) + n.choose r

notation:100 r "﹗" => Real.Gamma (r + 1)

theorem proposition_1_15 {n r : Nat} (h : n ≥ r) : n.choose r = (n !) / (r ! * (n - r)!) := by
  induction n generalizing r
  case zero => egg [choose, factorial, le_zero.mp h]
  case succ n hi =>
    by_cases hr : r = 0 <;> try subst hr
    all_goals try by_cases hn : r = n + 1 <;> try subst hn
    all_goals try simp; rw [Nat.div_self <| factorial_pos _]

    have fromReal : (n + 1)﹗ / (r﹗ * (n + 1 - r)﹗) = ↑((n + 1)! / (r ! * (n + 1 - r)!)) := by
      egg cast [Real.Gamma_nat_eq_factorial]
      · omega
      · sorry
      · rw [cast_ne_zero]; exact mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)

    have toReal : ↑((n !) / ((r - 1)! * (n - r + 1)!) + (n !) / (r ! * (n - r)!)) =
                  n﹗ / ((r - 1)﹗ * (n - r + 1)﹗) + n﹗ / (r ﹗ * (n - r)﹗) := by
      egg cast [Real.Gamma_nat_eq_factorial] <;> try omega
      · sorry
      · rw [cast_ne_zero]; exact mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)
      · sorry
      · rw [cast_ne_zero]; exact mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)

    have h₂ : n ≥ r                   := by omega
    have h₃ : n - (r - 1) = n - r + 1 := by omega
    have h₄ : (n : Real) - r + 1 ≠ 0  := by rw [←cast_one, ←cast_sub h₂, ←cast_add, cast_ne_zero]; omega
    have h₅ : (r : Real) ≠ 0          := by rw [cast_ne_zero, ne_eq]; exact hr
    have h₆ : (n : Real) + 1 ≠ 0      := by rw [←cast_one, ←cast_add, cast_ne_zero]; omega

    calc
      _ = (n !) / ((r - 1)! * (n - r + 1)!) + (n !) / (r ! * (n - r)!) := by egg [proposition_1_14, hi, h₃] <;> omega
      _ = _ := cast_inj (R := Real) |>.mp ?_

    set_option egg.conditionSubgoals true in
    calc
      _ = (n﹗ / ((r - 1)﹗ * (n - r + 1)﹗) + n﹗ / (r ﹗ * (n - r)﹗))           := by egg real [Real.Gamma_add_one, toReal, fromReal]
      _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * (1 / (n - r + 1) + 1 / r)               := by egg real [Real.Gamma_add_one, toReal, fromReal] <;> assumption
      _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * ((r + (n - r + 1)) / (r * (n - r + 1))) := by egg real [Real.Gamma_add_one, toReal, fromReal] <;> assumption
      _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * ((n + 1) / (r * (n - r + 1)))           := by egg real [Real.Gamma_add_one, toReal, fromReal]
      _ = (n + 1)﹗ / (r﹗ * (n + 1 - r)﹗)                                       := by egg real [Real.Gamma_add_one, toReal, fromReal] <;> assumption
      _ = _                                                                      := by egg real [Real.Gamma_add_one, toReal, fromReal]



    /-
    set_option egg.conditionSubgoals false in
    egg real calc [Real.Gamma_add_one, *] -- toReal, fromReal, h₄, h₅, h₆
      _ = (n﹗ / ((r - 1)﹗ * (n - r + 1)﹗) + n﹗ / (r ﹗ * (n - r)﹗))
      _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * (1 / (n - r + 1) + 1 / r)
      _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * ((r + (n - r + 1)) / (r * (n - r + 1)))
      _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * ((n + 1) / (r * (n - r + 1)))
      _ = (n + 1)﹗ / (r﹗ * (n + 1 - r)﹗)
      _ = _
    -/
