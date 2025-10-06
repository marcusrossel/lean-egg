import Mathlib
import Math.Comparisons.Simp

open Nat

notation:100 r "﹗" => Real.Gamma (r + 1)

set_option grind.warning false

attribute [rotman_simp] Real.Gamma_nat_eq_factorial Real.Gamma_add_one cast_zero cast_one cast_succ
                  cast_pred cast_add_one cast_add cast_sub cast_mul cast_div cast_pow cast_dvd_cast
                  cast_id cast_ite add_comm add_assoc add_zero sub_zero zero_sub mul_comm mul_assoc
                  mul_zero mul_one div_one zero_div add_div mul_div_mul_left mul_div_mul_right
                  mul_div_mul_comm div_mul_div_cancel _root_.div_mul_div_comm
                  div_mul_eq_div_mul_one_div sub_sub sub_add add_sub add_comm_sub sub_add_cancel
                  sub_add_eq_add_sub left_distrib right_distrib add_div_eq_mul_add_div

attribute [grind _=_] Real.Gamma_nat_eq_factorial
attribute [grind _=_] Real.Gamma_add_one
attribute [grind _=_] cast_zero
attribute [grind _=_] cast_one
attribute [grind _=_] cast_succ
attribute [grind _=_] cast_pred
attribute [grind _=_] cast_add_one
attribute [grind _=_] cast_add
attribute [grind _=_] cast_sub
attribute [grind _=_] cast_mul
attribute [grind _=_] cast_div
attribute [grind _=_] cast_pow
attribute [grind ←]   cast_dvd_cast
attribute [grind]     cast_id
-- attribute [grind?] cast_ite
attribute [grind _=_] add_comm
attribute [grind _=_] add_assoc
attribute [grind]     add_zero
attribute [grind]     sub_zero
attribute [grind _=_] zero_sub
attribute [grind _=_] mul_comm
attribute [grind _=_] mul_assoc
attribute [grind]     mul_zero
attribute [grind]     mul_one
attribute [grind]     div_one
attribute [grind]     zero_div
attribute [grind _=_] add_div
attribute [grind]     mul_div_mul_left
attribute [grind]     mul_div_mul_right
attribute [grind]     mul_div_mul_comm
attribute [grind]     div_mul_div_cancel
attribute [grind _=_] _root_.div_mul_div_comm
attribute [grind _=_] div_mul_eq_div_mul_one_div
attribute [grind _=_] sub_sub
attribute [grind _=_] sub_add
attribute [grind _=_] add_sub
attribute [grind _=_] add_comm_sub
attribute [grind]     sub_add_cancel
attribute [grind _=_] sub_add_eq_add_sub
attribute [grind _=_] left_distrib
attribute [grind _=_] right_distrib
attribute [grind _=_] add_div_eq_mul_add_div

theorem proposition_1_15 {n r : Nat} (h : n ≥ r) : n.choose r = (n !) / (r ! * (n - r)!) := by
  induction n generalizing r
  case zero => sorry
  case succ n ih =>
    by_cases hr : r = 0 <;> try subst hr
    all_goals try by_cases hn : r = n + 1 <;> try subst hn
    all_goals try simp; rw [Nat.div_self <| factorial_pos _]
    have ho : (n - r + 1) = n - (r - 1) := by omega

    calc
      _ = (n !) / ((r - 1)! * (n - r + 1)!) + (n !) / (r ! * (n - r)!) := by sorry
      _ = _ := cast_inj (R := Real) |>.mp ?_

    have : (r ! * (n + 1 - r)! : Real) ≠ 0 := sorry
    have : r ! * (n + 1 - r)! ∣ (n + 1)! := sorry
    have : r ≤ n + 1 := sorry
    have : (n : Real) + 1 ≠ 0 := sorry
    have : (n : Real) + 1 - (r : Real) ≠ 0 := sorry
    have : (n : Real) ≠ 0 := sorry
    have : (n : Real) - (r : Real) + 1 ≠ 0 := sorry
    have : (r : Real) ≠ 0 := sorry
    have : 0 < r := sorry
    have : ((r - 1)! * (n - r + 1)! : Real) ≠ 0 := sorry
    have : (r - 1)! * (n - r + 1)! ∣ n ! := sorry
    have : (r : Real)﹗ * ((n : Real) - (r : Real))﹗ ≠ 0 := sorry
    have : r ≤ n := sorry
    have : (r ! * (n - r)! : Real) ≠ 0 := sorry
    have : r ! * (n - r)! ∣ n ! := sorry

    calc
      _ = n﹗ / ((r - 1)﹗ * (n - r + 1)﹗) + n﹗ / (r﹗ * (n - r)﹗)              := by grind
      _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * (1 / (n - r + 1) + 1 / r)               := by grind
      _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * ((r + (n - r + 1)) / (r * (n - r + 1))) := by grind
      _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * ((n + 1) / (r * (n - r + 1)))           := by grind
      _ = (n + 1)﹗ / (r﹗ * (n + 1 - r)﹗)                                       := by grind
      _ = _                                                                      := by grind

example {n r : Nat} (h : n ≥ r) : n.choose r = (n !) / (r ! * (n - r)!) := by
  induction n generalizing r
  case zero => sorry
  case succ n ih =>
    by_cases hr : r = 0 <;> try subst hr
    all_goals try by_cases hn : r = n + 1 <;> try subst hn
    all_goals try simp; rw [Nat.div_self <| factorial_pos _]
    have ho : (n - r + 1) = n - (r - 1) := by omega

    calc
      _ = (n !) / ((r - 1)! * (n - r + 1)!) + (n !) / (r ! * (n - r)!) := by sorry
      _ = _ := cast_inj (R := Real) |>.mp ?_

    have : (r ! * (n + 1 - r)! : Real) ≠ 0 := sorry
    have : r ! * (n + 1 - r)! ∣ (n + 1)! := sorry
    have : r ≤ n + 1 := sorry
    have : (n : Real) + 1 ≠ 0 := sorry
    have : (n : Real) + 1 - (r : Real) ≠ 0 := sorry
    have : (n : Real) ≠ 0 := sorry
    have : (n : Real) - (r : Real) + 1 ≠ 0 := sorry
    have : (r : Real) ≠ 0 := sorry
    have : 0 < r := sorry
    have : ((r - 1)! * (n - r + 1)! : Real) ≠ 0 := sorry
    have : (r - 1)! * (n - r + 1)! ∣ n ! := sorry
    have : (r : Real)﹗ * ((n : Real) - (r : Real))﹗ ≠ 0 := sorry
    have : r ≤ n := sorry
    have : (r ! * (n - r)! : Real) ≠ 0 := sorry
    have : r ! * (n - r)! ∣ n ! := sorry

    calc
      _ = n﹗ / ((r - 1)﹗ * (n - r + 1)﹗) + n﹗ / (r﹗ * (n - r)﹗)              := by (fail_if_success simp only [rotman_simp, *); sorry
      _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * (1 / (n - r + 1) + 1 / r)               := by (fail_if_success simp only [rotman_simp, *); sorry
      _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * ((r + (n - r + 1)) / (r * (n - r + 1))) := by (fail_if_success simp only [rotman_simp, *); sorry
      _ = n﹗ / ((r - 1)﹗ * (n - r)﹗) * ((n + 1) / (r * (n - r + 1)))           := by (fail_if_success simp only [rotman_simp, *); sorry
      _ = (n + 1)﹗ / (r﹗ * (n + 1 - r)﹗)                                       := by (fail_if_success simp only [rotman_simp, *); sorry
      _ = _                                                                      := by (fail_if_success simp only [rotman_simp, *); sorry
