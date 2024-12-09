import Egg

set_option egg.shapes true

/--
info: [egg.encoded] Encoded
  [egg.encoded] Goal
    [egg.encoded] LHS: (◇ * (const "Bool.true"))
    [egg.encoded] RHS: (◇ * (const "Bool.true"))
-/
#guard_msgs in
set_option trace.egg.encoded true in
set_option egg.genTcProjRws false in
set_option egg.builtins false in
example : true = true := by
  egg

/--
info: [egg.encoded] Encoded
  [egg.encoded] Goal
    [egg.encoded] LHS: (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (app (◇ (→ * (→ * (→ * *))) (app (◇ (→ * (→ * (→ * (→ * *)))) (app (◇ (→ * (→ * (→ * (→ * (→ * *))))) (app (◇ (→ * (→ * (→ * (→ * (→ * (→ * *)))))) (const "HAdd.hAdd" 0 0 0)) (◇ * (const "Nat")))) (◇ * (const "Nat")))) (◇ * (const "Nat")))) (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (const "instHAdd" 0)) (◇ * (const "Nat")))) (◇ * (const "instAddNat")))))) (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (app (◇ (→ * (→ * (→ * *))) (const "OfNat.ofNat" 0)) (◇ * (const "Nat")))) (◇ * (lit 0)))) (◇ * (app (◇ (→ * *) (const "instOfNatNat")) (◇ * (lit 0)))))))) (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (app (◇ (→ * (→ * (→ * *))) (const "OfNat.ofNat" 0)) (◇ * (const "Nat")))) (◇ * (lit 1)))) (◇ * (app (◇ (→ * *) (const "instOfNatNat")) (◇ * (lit 1))))))))
    [egg.encoded] RHS: (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (app (◇ (→ * (→ * (→ * *))) (app (◇ (→ * (→ * (→ * (→ * *)))) (app (◇ (→ * (→ * (→ * (→ * (→ * *))))) (app (◇ (→ * (→ * (→ * (→ * (→ * (→ * *)))))) (const "HAdd.hAdd" 0 0 0)) (◇ * (const "Nat")))) (◇ * (const "Nat")))) (◇ * (const "Nat")))) (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (const "instHAdd" 0)) (◇ * (const "Nat")))) (◇ * (const "instAddNat")))))) (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (app (◇ (→ * (→ * (→ * *))) (const "OfNat.ofNat" 0)) (◇ * (const "Nat")))) (◇ * (lit 1)))) (◇ * (app (◇ (→ * *) (const "instOfNatNat")) (◇ * (lit 1)))))))) (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (app (◇ (→ * (→ * (→ * *))) (const "OfNat.ofNat" 0)) (◇ * (const "Nat")))) (◇ * (lit 0)))) (◇ * (app (◇ (→ * *) (const "instOfNatNat")) (◇ * (lit 0))))))))
  [egg.encoded] #0(⇔)
    [egg.encoded] LHS: (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (app (◇ (→ * (→ * (→ * *))) (app (◇ (→ * (→ * (→ * (→ * *)))) (app (◇ (→ * (→ * (→ * (→ * (→ * *))))) (app (◇ (→ * (→ * (→ * (→ * (→ * (→ * *)))))) (const "HAdd.hAdd" 0 0 0)) (◇ * (const "Nat")))) (◇ * (const "Nat")))) (◇ * (const "Nat")))) (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (const "instHAdd" 0)) (◇ * (const "Nat")))) (◇ * (const "instAddNat")))))) (◇ * ?354))) (◇ * ?355)))
    [egg.encoded] RHS: (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (app (◇ (→ * (→ * (→ * *))) (app (◇ (→ * (→ * (→ * (→ * *)))) (app (◇ (→ * (→ * (→ * (→ * (→ * *))))) (app (◇ (→ * (→ * (→ * (→ * (→ * (→ * *)))))) (const "HAdd.hAdd" 0 0 0)) (◇ * (const "Nat")))) (◇ * (const "Nat")))) (◇ * (const "Nat")))) (◇ * (app (◇ (→ * *) (app (◇ (→ * (→ * *)) (const "instHAdd" 0)) (◇ * (const "Nat")))) (◇ * (const "instAddNat")))))) (◇ * ?355))) (◇ * ?354)))
    [egg.encoded] No Conditions
-/
#guard_msgs in
set_option trace.egg.encoded true in
set_option egg.genTcProjRws false in
set_option egg.builtins false in
example (h : ∀ x y : Nat, x + y = y + x) : 0 + 1 = 1 + 0 := by
  egg [h]

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
example (h : ∀ u : Unit, u = .unit) : Nat.add = Nat.mul := by
  egg (config := { exitPoint := some .beforeProof }) [h]

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

example : (fun _ : Nat => 0) = (fun _ => 0 + 0) := by
  egg [Nat.add_zero]

example : (fun x => x) = (fun x => x + 0) := by
  egg [Nat.add_zero]

example : (fun x => x) = (fun x => 0 + 0 + x) := by
  egg [Nat.zero_add]

example : (fun x => x) = (fun x => 0 + x) := by
  egg [Nat.zero_add]

example (f : (Nat → Nat) → Bool) : f (fun x => x) = f (fun x => x + 0) := by
  egg [Nat.add_zero]

example (h : ∀ x y : Nat, x = y ↔ y = x) : (∀ x y : Nat, x = y) ↔ (∀ a b : Nat, b = a + 0) := by
  egg [h, Nat.add_zero]

end Binders

section «Class Def»

def Mul.pow [Mul α] [OfNat α 1] (a : α) : Nat → α
  | 0     => 1
  | n + 1 => a * (pow a n)

instance mulPow [Mul α] [OfNat α 1] : Pow α Nat where
  pow := Mul.pow

example [Mul α] [OfNat α 1] (a : α) : Mul.pow a 0 = (1 : α) := by
  egg [Mul.pow]

example [Mul α] [OfNat α 1] (a : α) : a ^ 0 = (1 : α) := by
  egg [Mul.pow]

end «Class Def»

section Groups

class One (α) where one : α

instance [One α] : OfNat α 1 where ofNat := One.one

class Inv (α : Type u) where
  inv : α → α

postfix:max "⁻¹" => Inv.inv

class Group (α) extends One α, Inv α, Mul α where
  mul_assoc     (a b c : α) : (a * b) * c = a * (b * c)
  one_mul       (a : α)     : 1 * a = a
  mul_one       (a : α)     : a * 1 = a
  inv_mul_self  (a : α)     : a⁻¹ * a = 1
  mul_inv_self  (a : α)     : a * a⁻¹ = 1

variable [Group G] {a b : G}

open Group Egg.Guides Egg.Config.Modifier in
macro "group" mod:egg_cfg_mod base:(egg_base)? guides:(egg_guides)? : tactic => `(tactic|
  egg $mod [mul_assoc, one_mul, mul_one, inv_mul_self, mul_inv_self] $[$base]? $[$guides]?
)

theorem inv_mul_cancel_left : a⁻¹ * (a * b) = b := by group

theorem mul_inv_cancel_left : a * (a⁻¹ * b) = b := by group

theorem inv_one : (1 : G)⁻¹ = 1 := by group

theorem inv_mul : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  calc _ = b⁻¹ * a⁻¹ * (a * b) * (a * b)⁻¹ := by group
       _ = _                               := by group

theorem inv_inv : a⁻¹⁻¹ = a := by
  calc _ = a⁻¹⁻¹ * (a⁻¹ * a) := by group
       _ = _                 := by group

set_option egg.timeLimit 3 in
theorem inv_mul' : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  group using b⁻¹ * a⁻¹ * (a * b) * (a * b)⁻¹

theorem inv_inv' : a⁻¹⁻¹ = a := by
  group using a⁻¹ * a

end Groups
