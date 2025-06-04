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

notation:100 r "﹗" => Real.Gamma (r + 1)

theorem proposition_1_15 {n r : Nat} (h : n ≥ r) : n.choose r = (n !) / (r ! * (n - r)!) := by
  induction n generalizing r
  case zero => egg [choose, factorial, le_zero.mp h]
  case succ n ih =>
    by_cases hr : r = 0 <;> try subst hr
    all_goals try by_cases hn : r = n + 1 <;> try subst hn
    all_goals try simp; rw [Nat.div_self <| factorial_pos _]
    have ho : (n - r + 1) = n - (r - 1) := by omega

    calc
      _ = (n !) / ((r - 1)! * (n - r + 1)!) + (n !) / (r ! * (n - r)!) := by egg [choose_succ_left, ih, ho] <;> omega
      _ = _ := cast_inj (R := Real) |>.mp ?_

    egg +cast +real calc [Real.Gamma_nat_eq_factorial, Real.Gamma_add_one]
      _ = n﹗ / ((r - 1)﹗ * (n - r + 1)﹗) + n﹗ / (r ﹗ * (n - r)﹗)
      _ = (n﹗ / ((r - 1)﹗ * (n - r + 1)﹗) + n﹗ / (r ﹗ * (n - r)﹗))
      _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * (1 / (n - r + 1) + 1 / r)
      _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * ((r + (n - r + 1)) / (r * (n - r + 1)))
      _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * ((n + 1) / (r * (n - r + 1)))
      _ = (n + 1)﹗ / (r﹗ * (n + 1 - r)﹗)
      _ = _

    all_goals try omega
    · rw [cast_ne_zero]; exact mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)
    · exact factorial_mul_factorial_dvd_factorial h
    · rw [←cast_one, ←cast_add, cast_ne_zero]; omega
    · rw [cast_ne_zero]; omega
    · rw [←cast_one, ←cast_sub (by omega : n ≥ r), ←cast_add, cast_ne_zero]; omega
    · rw [cast_ne_zero]; exact mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)
    · exact factorial_mul_factorial_dvd_factorial <| by omega
    · rw [cast_ne_zero]; exact mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)
    · exact ho ▸ factorial_mul_factorial_dvd_factorial (sub_le_of_le_add h)
