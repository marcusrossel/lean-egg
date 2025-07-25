import Egg

set_option egg.shapes true

/--
trace: [egg.encoded] Encoded
  [egg.encoded] Goal
    [egg.encoded] LHS: (◇ * (const "Bool.true"))
    [egg.encoded] RHS: (◇ * (const "Bool.true"))
  [egg.encoded] Guides
    [egg.encoded] (◇ * (= (◇ * (const "Bool.true")) (◇ * (const "Bool.true"))))
-/
#guard_msgs in
set_option trace.egg.encoded true in
set_option egg.tcProjs false in
set_option egg.builtins false in
example : true = true := by
  egg

/-
info: [egg.encoded] Encoded
  [egg.encoded] Goal
    [egg.encoded] LHS: (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (app (◇ (→ * (→ * (→ * *))) (app (◇ (→ * (→ * (→ * (→ * *)))) (app (◇ (→ * (→ * (→ * (→ * (→ * *))))) (app (◇ (→ * (→ * (→ * (→ * (→ * (→ * *)))))) (const "HAdd.hAdd" 0 0 0)) (◇ * (const "Nat")))) (◇ * (const "Nat")))) (◇ * (const "Nat")))) (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (const "instHAdd" 0)) (◇ * (const "Nat")))) (◇ * (const "instAddNat")))))) (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (app (◇ (→ * (→ * (→ * *))) (const "OfNat.ofNat" 0)) (◇ * (const "Nat")))) (◇ * (lit 0)))) (◇ * (app (◇ (→ * *) (const "instOfNatNat")) (◇ * (lit 0)))))))) (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (app (◇ (→ * (→ * (→ * *))) (const "OfNat.ofNat" 0)) (◇ * (const "Nat")))) (◇ * (lit 1)))) (◇ * (app (◇ (→ * *) (const "instOfNatNat")) (◇ * (lit 1))))))))
    [egg.encoded] RHS: (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (app (◇ (→ * (→ * (→ * *))) (app (◇ (→ * (→ * (→ * (→ * *)))) (app (◇ (→ * (→ * (→ * (→ * (→ * *))))) (app (◇ (→ * (→ * (→ * (→ * (→ * (→ * *)))))) (const "HAdd.hAdd" 0 0 0)) (◇ * (const "Nat")))) (◇ * (const "Nat")))) (◇ * (const "Nat")))) (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (const "instHAdd" 0)) (◇ * (const "Nat")))) (◇ * (const "instAddNat")))))) (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (app (◇ (→ * (→ * (→ * *))) (const "OfNat.ofNat" 0)) (◇ * (const "Nat")))) (◇ * (lit 1)))) (◇ * (app (◇ (→ * *) (const "instOfNatNat")) (◇ * (lit 1)))))))) (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (app (◇ (→ * (→ * (→ * *))) (const "OfNat.ofNat" 0)) (◇ * (const "Nat")))) (◇ * (lit 0)))) (◇ * (app (◇ (→ * *) (const "instOfNatNat")) (◇ * (lit 0))))))))
  [egg.encoded] #0(⇔)
    [egg.encoded] LHS: (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (app (◇ (→ * (→ * (→ * *))) (app (◇ (→ * (→ * (→ * (→ * *)))) (app (◇ (→ * (→ * (→ * (→ * (→ * *))))) (app (◇ (→ * (→ * (→ * (→ * (→ * (→ * *)))))) (const "HAdd.hAdd" 0 0 0)) (◇ * (const "Nat")))) (◇ * (const "Nat")))) (◇ * (const "Nat")))) (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (const "instHAdd" 0)) (◇ * (const "Nat")))) (◇ * (const "instAddNat")))))) (◇ * ?351))) (◇ * ?352)))
    [egg.encoded] RHS: (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (app (◇ (→ * (→ * (→ * *))) (app (◇ (→ * (→ * (→ * (→ * *)))) (app (◇ (→ * (→ * (→ * (→ * (→ * *))))) (app (◇ (→ * (→ * (→ * (→ * (→ * (→ * *)))))) (const "HAdd.hAdd" 0 0 0)) (◇ * (const "Nat")))) (◇ * (const "Nat")))) (◇ * (const "Nat")))) (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (const "instHAdd" 0)) (◇ * (const "Nat")))) (◇ * (const "instAddNat")))))) (◇ * ?352))) (◇ * ?351)))
    [egg.encoded] No Conditions
  [egg.encoded] Guides
    [egg.encoded] (◇ (→ * (→ * *)) (app (◇ (→ * (→ * (→ * *))) (app (◇ (→ * (→ * (→ * (→ * *)))) (app (◇ (→ * (→ * (→ * (→ * (→ * *))))) (app (◇ (→ * (→ * (→ * (→ * (→ * (→ * *)))))) (const "HAdd.hAdd" 0 0 0)) (◇ * (const "Nat")))) (◇ * (const "Nat")))) (◇ * (const "Nat")))) (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (const "instHAdd" 0)) (◇ * (const "Nat")))) (◇ * (const "instAddNat"))))))
-/
-- #guard_msgs in
set_option trace.egg.encoded true in
set_option egg.tcProjs false in
set_option egg.builtins false in
example (h : ∀ x y : Nat, x + y = y + x) : 0 + 1 = 1 + 0 := by
  -- TODO: How should shapes interact with erased terms?
  sorry -- egg [h]

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
example (h : ∀ (f : Unit → Unit) (u : Unit), f u = .unit) : id Nat.add = id Nat.mul := by
  egg [h]

section Basic

example (a : Nat) : a = a := by
  egg

example (a b : Nat) (h : a = b) : a = b := by
  egg [h]

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  egg [h₁, h₂]

example (a b : Nat) : a + b = b + a := by
  egg [Nat.add_comm]

example (a b c : Nat) : (a + b) + c = (c + b) + a := by
  egg [Nat.add_comm, Nat.add_assoc]

example (a : Nat) (h : ∀ x : Nat, x + 1 = 1 + x) : a + 1 = 1 + a := by
  egg [h]

def f : Nat → Nat
  | .zero   => .zero
  | .succ n => f n

def g : Nat → Nat
  | .zero   => .zero
  | .succ n => g n

example : f (g Nat.zero.succ.succ) = .zero := by
  egg [f, g]

end Basic

section Binders

-- TODO: Cf. the TODO above.

example : (fun _ : Nat => 0) = (fun _ => 0 + 0) := by
  sorry -- egg [Nat.add_zero]

example : (fun x => x) = (fun x => x + 0) := by
  sorry -- egg [Nat.add_zero]

example : (fun x => x) = (fun x => 0 + 0 + x) := by
  sorry -- egg [Nat.zero_add]

example : (fun x => x) = (fun x => 0 + x) := by
  sorry -- egg [Nat.zero_add]

example (f : (Nat → Nat) → Bool) : f (fun x => x) = f (fun x => x + 0) := by
  sorry -- egg [Nat.add_zero]

example (h : ∀ x y : Nat, x = y ↔ y = x) : (∀ x y : Nat, x = y) ↔ (∀ a b : Nat, b = a + 0) := by
  sorry -- egg [h, Nat.add_zero]

end Binders

section «Class Def»

def Mul.pow [Mul α] [One α] (a : α) : Nat → α
  | 0     => 1
  | n + 1 => a * (pow a n)

instance mulPow [Mul α] [One α] : Pow α Nat where
  pow := Mul.pow

example [Mul α] [One α] (a : α) : Mul.pow a 0 = (1 : α) := by
  egg [Mul.pow]

example [Mul α] [One α] (a : α) : a ^ 0 = (1 : α) := by
  egg [Mul.pow]

end «Class Def»

section Groups

class Group (α) extends One α, Inv α, Mul α where
  mul_assoc     (a b c : α) : (a * b) * c = a * (b * c)
  one_mul       (a : α)     : 1 * a = a
  mul_one       (a : α)     : a * 1 = a
  inv_mul_self  (a : α)     : a⁻¹ * a = 1
  mul_inv_self  (a : α)     : a * a⁻¹ = 1

variable [Group G] {a b : G}

open Group Egg.Guides Egg.Config.Modifier in
macro "group" mod:egg_cfg_mod guides:(egg_guides)? : tactic => `(tactic|
  egg $mod:egg_cfg_mod [mul_assoc, one_mul, mul_one, inv_mul_self, mul_inv_self] $[$guides]?
)

theorem inv_mul_cancel_left : a⁻¹ * (a * b) = b := by group

theorem mul_inv_cancel_left : a * (a⁻¹ * b) = b := by group

theorem inv_one : (1 : G)⁻¹ = 1 := by
  group using 1 * (1 : G)⁻¹

theorem inv_mul : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  calc _ = b⁻¹ * a⁻¹ * (a * b) * (a * b)⁻¹ := by group
       _ = _                               := by group

theorem inv_inv : a⁻¹⁻¹ = a := by
  calc _ = a⁻¹⁻¹ * (a⁻¹ * a) := by group
       _ = _                 := by group

theorem inv_mul' : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  group using b⁻¹ * a⁻¹ * (a * b) * (a * b)⁻¹

theorem inv_inv' : a⁻¹⁻¹ = a := by
  group using a⁻¹⁻¹ * a⁻¹ * a

end Groups
