import Egg

axiom G : Type
axiom G.mul : G → G → G
axiom G.one : G
axiom G.inv : G → G

noncomputable instance : Mul G where
  mul := G.mul

set_option hygiene false in
macro "ges" : tactic => `(tactic| egg [assocMul, invLeft, mulOne, oneMul, invRight])

open G

variable
  (assocMul: ∀ (a b c : G), a * (b * c) = (a * b) * c)
  (invLeft: ∀ (a : G), (inv a) * a = one)
  (oneMul: ∀ (a : G), one * a = a)
  (mulOne: ∀ (a : G), a * one = a)
  (invRight: ∀ (a : G), a * (inv a) = one)
  (x y : G)

theorem inv_inv : inv (inv x) = x := by
  calc
    inv (inv x) = (inv (inv x)) * ((inv x) * x) := by ges
              _ = x                             := by ges

theorem inv_mul_cancel_left : (inv x) * (x * y) = y := by
  ges

theorem mul_inv_cancel_left : x * ((inv x) * y) = y := by
  ges

theorem inv_mul : inv (x * y) = (inv y) * (inv x) := by
  calc
    inv (x * y) = (inv (x * y)) * (x * (inv x)) := by ges
              _ = (inv (x * y)) * (x * (y * inv y) * (inv x)) := by ges
              _ = (inv (x * y)) * (x * y) * (inv y * inv x) := by ges
              _ = one * (inv y * inv x) := by ges
              _ = inv y * inv x := by ges

theorem one_inv : (inv one) = one := by
  ges
