import Egg
import Lean

open Lean Meta Elab Term Tactic IO in
elab "timed " t:tactic : tactic => do
  let before ← monoMsNow
  evalTactic t
  let after ← monoMsNow
  logInfo s!"{after - before}ms"

axiom G : Type
axiom G.mul : G → G → G
axiom G.one : G
axiom G.inv : G → G

noncomputable instance : Mul G := ⟨G.mul⟩

set_option hygiene false in
macro "ges" : tactic => `(tactic| egg [assocMul, invLeft, mulOne, oneMul, invRight])

open G

theorem inv_inv
  (assocMul: forall (a b c: G), a * (b * c) = (a * b) * c)
  (invLeft: forall (a: G), (inv a) * a = one)
  (oneMul: forall (a: G), one * a = a)
  (mulOne: forall (a: G), a * one = a)
  (invRight: forall (a: G), a * (inv a) = one)
  (x: G)
  : (inv (inv x) = x) := by
    timed egg [assocMul, invLeft, mulOne, oneMul, invRight] using (inv x) * x

theorem inv_mul_cancel_left
  (assocMul: forall (a b c: G), a * (b * c) = (a * b) * c)
  (invLeft: forall (a: G), (inv a) * a = one)
  (oneMul: forall (a: G), one * a = a)
  (mulOne: forall (a: G), a * one = a)
  (invRight: forall (a: G), a * (inv a) = one)
  (x: G)
  (x y : G)
  : ((inv x) * (x * y)) = y := by timed ges


theorem mul_inv_cancel_left
  (assocMul: forall (a b c: G), a * (b * c) = (a * b) * c)
  (invLeft: forall (a: G), (inv a) * a = one)
  (oneMul: forall (a: G), one * a = a)
  (mulOne: forall (a: G), a * one = a)
  (invRight: forall (a: G), a * (inv a) = one)
  (x y : G)
  : x * ((inv x) * y) = y := by timed ges

theorem inv_mul
  (assocMul: forall (a b c: G), a * (b * c) = (a * b) * c)
  (invLeft: forall (a: G), (inv a) * a = one)
  (oneMul: forall (a: G), one * a = a)
  (mulOne: forall (a: G), a * one = a)
  (invRight: forall (a: G), a * (inv a) = one)
  (x y : G)
  : (inv (x * y)) = (inv y) * (inv x) := by
    timed egg [assocMul, invLeft, mulOne, oneMul, invRight] using (x * y) * (inv (x * y))

theorem one_inv
  (assocMul: forall (a b c: G), a * (b * c) = (a * b) * c)
  (invLeft: forall (a: G), (inv a) * a = one)
  (oneMul: forall (a: G), one * a = a)
  (mulOne: forall (a: G), a * one = a)
  (invRight: forall (a: G), a * (inv a) = one)
  : (inv one) = one := by timed ges
