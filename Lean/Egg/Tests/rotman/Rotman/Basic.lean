import Mathlib
import Egg

-- TODO: Could egg be a good tactic for converting between representations, assuming we can get the
--       required condition subgoals as output? Problem is that this doesn't even work:
--
--set_option trace.egg true in
-- set_option egg.genGoalTcSpec true in
-- example (a b : Nat) : ↑(a + b) = (a : Real) + b := by
--   egg [cast_add]

open Lean Egg.Guides Egg.Config.Modifier in
macro "egg_main" mod:egg_cfg_mod prems:egg_premises base:(egg_base)? guides:(egg_guides)? : tactic => do
  let mut rws : Array (TSyntax `egg_premise) := #[]
  let mut facts : Option (Array (TSyntax `egg_premise)) := none
  if let `(egg_premises| [$rs,* $[; $fs,*]?]) := prems then rws := rs; facts := fs
  `(tactic|
    set_option egg.genGoalTcSpec true in
    set_option egg.genBetaRw false in
    egg $mod [add_comm, add_assoc, mul_comm, mul_assoc, sub_add_cancel, $rws,* $[; $facts,*]?]
    $[$base]? $[$guides]?
  )

-- From Rotman
axiom proposition_1_14 (n r : Nat) : (n + 1).choose r = n.choose (r - 1) + n.choose r

notation:100 r "¡" => Real.Gamma (r + 1)

open Nat

theorem proposition_1_15 {n r : Nat} (h : n ≥ r) : n.choose r = (n !) / (r ! * (n - r)!) := by
  induction n generalizing r
  case zero => rw [Nat.le_zero.mp h]; rfl
  case succ n hi =>
    by_cases hr : r = 0 <;> try subst hr
    all_goals try by_cases hn : r = n + 1 <;> try subst hn
    all_goals try simp; rw [Nat.div_self <| factorial_pos _]

    have fromReal : (n + 1)¡ / (r¡ * (n + 1 - r)¡) = ↑((n + 1)! / (r ! * (n + 1 - r)!)) := by
      have h₁ : r ≤ n + 1                          := by omega
      have h₂ : (r ! * (n + 1 - r)!) ∣ (n + 1)!    := sorry
      have h₃ : ↑(r ! * (n + 1 - r)!) ≠ (0 : Real) := by rw [cast_ne_zero]; exact mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)
      rw (config := { occs := .pos [1, 4]}) [←cast_one]
      simp only [←cast_add, ←cast_mul, ←cast_sub, h₁, ←cast_div h₂ h₃, Real.Gamma_nat_eq_factorial]

    have toReal : ↑((n !) / ((r - 1)! * (n - r + 1)!) + (n !) / (r ! * (n - r)!)) = (n¡ / ((r - 1)¡ * (n - r + 1)¡) + n¡ / (r ¡ * (n - r)¡)) := by
      have h₁ : 1 ≤ r                                   := by omega
      have h₂ : r ≤ n                                   := by omega
      have h₃ : (r ! * (n - r)!) ∣ (n !)                := sorry
      have h₄ : ↑(r ! * (n - r)!) ≠ (0 : Real)          := by rw [cast_ne_zero]; exact mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)
      have h₅ : ((r - 1)! * (n - r + 1)!) ∣ (n !)       := sorry
      have h₆ : ↑((r - 1)! * (n - r + 1)!) ≠ (0 : Real) := by rw [cast_ne_zero]; exact mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)
      rw (config := { occs := .pos [4, 6]}) [←cast_one]
      simp only [←cast_add, ←cast_mul, ←cast_sub, h₁, h₂, ←cast_div h₃ h₄, ←cast_div h₅ h₆, Real.Gamma_nat_eq_factorial]

    have h₁ : n ≥ r - 1               := by omega
    have h₂ : n ≥ r                   := by omega
    have h₃ : n - (r - 1) = n - r + 1 := by omega
    have h₄ : (n : Real) - r + 1 ≠ 0  := by rw [←cast_one, ←cast_sub h₂, ←cast_add, cast_ne_zero]; omega
    have h₅ : (r : Real) ≠ 0          := by rw [cast_ne_zero, ne_eq]; exact hr
    have h₆ : (n : Real) + 1 ≠ 0      := by rw [←cast_one, ←cast_add, cast_ne_zero]; omega
    calc
      _ = (n !) / ((r - 1)! * (n - r + 1)!) + (n !) / (r ! * (n - r)!) := by egg [proposition_1_14, hi h₁, hi h₂, h₃]
      _ = _ := Nat.cast_inj.mp <|
        calc ↑((n !) / ((r - 1)! * (n - r + 1)!) + (n !) / (r ! * (n - r)!))
          _ = (n¡ / ((r - 1)¡ * (n - r + 1)¡) + n¡ / (r ¡ * (n - r)¡))                               := toReal
          _ = n¡ / ((r - 1)¡ * (n - r)¡) * (1 / (n - r + 1) + 1 / r)                                 := by egg_main [Real.Gamma_add_one, div_mul_eq_div_mul_one_div, left_distrib (R := Real); h₄, h₅]
          _ = n¡ / ((r - 1)¡ * (n - r)¡) * (r / (r * (n - r + 1)) + (n - r + 1) / (r * (n - r + 1))) := by egg_main [mul_div_mul_left, mul_one; h₄, h₅]
          _ = (n + 1)¡ / (r¡ * (n + 1 - r)¡)                                                         := by egg_main [_root_.add_div, _root_.div_mul_div_comm, Real.Gamma_add_one, sub_add_eq_add_sub, Real.Gamma_add_one; h₄, h₅, h₆]
          _ = ↑((n + 1)! / (r ! * (n + 1 - r)!))                                                     := fromReal

/-
lemma proposition_1_15_main (h₁ : n - r + 1 ≠ 0) (h₂ : r ≠ 0) (h₃ : n + 1 ≠ 0) :
    n¡ / ((r - 1)¡ * (n - r + 1)¡) + n¡ / (r¡ * (n - r)¡) = (n + 1)¡ / (r¡ * (n + 1 - r)¡) := calc
  _ = n¡ / ((r - 1)¡ * (n - r)¡ * (n - r + 1)) + n¡ / ((r - 1)¡ * (n - r)¡ * r)              := by egg_main [Real.Gamma_add_one; h₁, h₂]
  _ = n¡ / ((r - 1)¡ * (n - r)¡) * (1 / (n - r + 1) + 1 / r)                                 := by egg_main [div_mul_eq_div_mul_one_div, left_distrib (R := Real)]
  _ = n¡ / ((r - 1)¡ * (n - r)¡) * (r / (r * (n - r + 1)) + (n - r + 1) / (r * (n - r + 1))) := by egg_main [mul_div_mul_left, mul_one; h₁, h₂]
  _ = n¡ / ((r - 1)¡ * (n - r)¡) * ((r + (n - r + 1)) / (r * (n - r + 1)))                   := by egg_main [_root_.add_div]
  _ = n¡ / ((r - 1)¡ * (n - r)¡) * ((n + 1) / (r * (n - r + 1)))                             := by egg_main
  _ = (n¡ * (n + 1)) / (r¡ * (n - r + 1)¡)                                                   := by egg_main [_root_.div_mul_div_comm, Real.Gamma_add_one; h₁, h₂]
  _ = (n + 1)¡ / (r¡ * (n + 1 - r)¡)                                                         := by egg_main [sub_add_eq_add_sub, Real.Gamma_add_one; h₃]

lemma proposition_1_15_main' (h₁ : n - r + 1 ≠ 0) (h₂ : r ≠ 0) (h₃ : n + 1 ≠ 0) :
    n¡ / ((r - 1)¡ * (n - r + 1)¡) + n¡ / (r¡ * (n - r)¡) = (n + 1)¡ / (r¡ * (n + 1 - r)¡) := calc
  _ = n¡ / ((r - 1)¡ * (n - r)¡) * (1 / (n - r + 1) + 1 / r)                                 := by egg_main [Real.Gamma_add_one, div_mul_eq_div_mul_one_div, left_distrib (R := Real); h₁, h₂]
  _ = n¡ / ((r - 1)¡ * (n - r)¡) * (r / (r * (n - r + 1)) + (n - r + 1) / (r * (n - r + 1))) := by egg_main [mul_div_mul_left, mul_one; h₁, h₂]
  _ = _                                                                                      := by egg_main [_root_.add_div, _root_.div_mul_div_comm, Real.Gamma_add_one, sub_add_eq_add_sub, Real.Gamma_add_one; h₁, h₂, h₃]
-/
