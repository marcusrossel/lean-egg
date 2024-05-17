import Mathlib
import Egg

-- From Rotman
axiom proposition_1_14 (n r : Nat) : (n + 1).choose r = n.choose (r - 1) + n.choose r

notation:100 r "¡" => Real.Gamma (r + 1)

open Lean Egg.Guides Egg.Config.Modifier in
macro "gamma" mod:egg_cfg_mod prems:egg_premises base:(egg_base)? guides:(egg_guides)? : tactic => do
  let mut rws : Array (TSyntax `egg_premise) := #[]
  let mut facts : Option (Array (TSyntax `egg_premise)) := none
  if let `(egg_premises| [$rs,* $[; $fs,*]?]) := prems then rws := rs; facts := fs
  `(tactic|
    set_option egg.genGoalTcSpec true in
    set_option egg.genBetaRw false in
    egg $mod [add_comm, add_assoc, mul_comm, mul_assoc, sub_add_cancel, $rws,* $[; $facts,*]?] $[$base]? $[$guides]?
  )

lemma proposition_1_15_aux (h₁ : n - r + 1 ≠ 0) (h₂ : r ≠ 0) (h₃ : n + 1 ≠ 0) :
    n¡ / ((r - 1)¡ * (n - r + 1)¡) + n¡ / (r¡ * (n - r)¡) = (n + 1)¡ / (r¡ * (n + 1 - r)¡) := calc
  _ = n¡ / ((r - 1)¡ * (n - r)¡ * (n - r + 1)) + n¡ / ((r - 1)¡ * (n - r)¡ * r)              := by gamma [Real.Gamma_add_one; h₁, h₂]
  _ = n¡ / ((r - 1)¡ * (n - r)¡) * (1 / (n - r + 1) + 1 / r)                                 := by gamma [div_mul_eq_div_mul_one_div, left_distrib (R := Real)]
  _ = n¡ / ((r - 1)¡ * (n - r)¡) * (r / (r * (n - r + 1)) + (n - r + 1) / (r * (n - r + 1))) := by gamma [mul_div_mul_left, mul_one; h₁, h₂]
  _ = n¡ / ((r - 1)¡ * (n - r)¡) * ((r + (n - r + 1)) / (r * (n - r + 1)))                   := by gamma [_root_.add_div]
  _ = n¡ / ((r - 1)¡ * (n - r)¡) * ((n + 1) / (r * (n - r + 1)))                             := by gamma
  _ = (n¡ * (n + 1)) / (r¡ * (n - r + 1)¡)                                                   := by gamma [_root_.div_mul_div_comm, Real.Gamma_add_one; h₁, h₂]
  _ = (n + 1)¡ / (r¡ * (n + 1 - r)¡)                                                         := by gamma [sub_add_eq_add_sub, Real.Gamma_add_one; h₃]

lemma proposition_1_15_aux' (h₁ : n - r + 1 ≠ 0) (h₂ : r ≠ 0) (h₃ : n + 1 ≠ 0) :
    n¡ / ((r - 1)¡ * (n - r + 1)¡) + n¡ / (r¡ * (n - r)¡) = (n + 1)¡ / (r¡ * (n + 1 - r)¡) := calc
  _ = n¡ / ((r - 1)¡ * (n - r)¡) * (1 / (n - r + 1) + 1 / r)                                 := by gamma [Real.Gamma_add_one, div_mul_eq_div_mul_one_div, left_distrib (R := Real); h₁, h₂]
  _ = n¡ / ((r - 1)¡ * (n - r)¡) * (r / (r * (n - r + 1)) + (n - r + 1) / (r * (n - r + 1))) := by gamma [mul_div_mul_left, mul_one; h₁, h₂]
  _ = _                                                                                      := by gamma [_root_.add_div, _root_.div_mul_div_comm, Real.Gamma_add_one, sub_add_eq_add_sub, Real.Gamma_add_one; h₁, h₂, h₃]

open Nat

theorem proposition_1_15 {n r : Nat} (h : n ≥ r) : n.choose r = (n !) / (r ! * (n - r)!) := by
  induction n generalizing r
  case zero => rw [Nat.le_zero.mp h]; rfl
  case succ n hi =>
    by_cases hr : r = 0 <;> try subst hr
    all_goals try by_cases hn : r = n + 1 <;> try subst hn
    all_goals try simp; rw [Nat.div_self <| factorial_pos _]

    have h₁ : n ≥ r - 1               := by omega
    have h₂ : n ≥ r                   := by omega
    have h₃ : n - (r - 1) = n - r + 1 := by omega
    have s₁ : (n + 1).choose r = (n !) / ((r - 1)! * (n - r + 1)!) + (n !) / (r ! * (n - r)!) := by egg [proposition_1_14, hi h₁, hi h₂, h₃]
    rw [s₁]
    sorry
