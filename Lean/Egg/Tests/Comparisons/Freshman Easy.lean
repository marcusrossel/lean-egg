import Egg
import Lean

open Lean Meta Elab Term Tactic IO in
elab "timed " t:tactic : tactic => do
  let before ← monoMsNow
  evalTactic t
  let after ← monoMsNow
  logInfo s!"{after - before}ms"

set_option hygiene false in
macro "ges3" : tactic => `(tactic| egg [comm_add, comm_mul, assoc_add, assoc_mul, add_assoc, mul_assoc, sub_canon, canon_sub, zero_add, zero_mul, one_mul, add_zero, mul_one, cancel_sub, distribute, factor, pow_mul, pow_one, pow_two, pow_three, pow_four, one_pow, two_pow, three_pow, four_pow, two_add, add_two, char_two])

set_option hygiene false
infixr:50 " + " => add
infixr:60 " * " => mul
notation l "^" r => pow l r

theorem freshmans_dream_3
  (R: Type )
  (add: R → R → R )
  (sub: R → R → R )
  (mul: R → R → R )
  (pow: R → R → R )
  (zero : R )
  (one: R )
  (two : R )
  (three : R )
  (four : R )
  (inv : R → R )
  (neg : R → R )
  (comm_add : forall a b : R,  (add a b)        = (add b a) )
  (comm_mul:  forall a b : R, (mul a b)        = (mul b a) )
  (assoc_add: forall a b c : R, (add a (add b c)) = (add (add a b) c) )
  (assoc_mul: forall a b c : R, (mul a (mul b c)) = (mul (mul a b) c) )
  (add_assoc: forall a b c : R, (add (add a b) c) = (add a (add b c)) )
  (mul_assoc: forall a b c : R, (mul (mul a b) c) = (mul a (mul b c)) )
  (sub_canon: forall a b : R, (sub a b) = (add a (mul (neg one) b)) )
  (canon_sub: forall a b : R, (add a (mul (neg one) b)) = (sub a b)  )
  (zero_add: forall a : R, (add a zero) = a )
  (zero_mul: forall a : R, (mul a zero) = zero )
  (one_mul: forall a : R,   (mul a one) = a )
  (add_zero: forall a : R,  a = (add a zero) )
  (mul_one: forall a : R,   a = (mul a one) )
  (cancel_sub: forall a : R,  (sub a a) = zero )
  (distribute: forall a b c : R, (mul a (add b c))        = (add (mul a b) (mul a c)) )
  (factor    : forall a b c : R, (add (mul a b) (mul a c)) = (mul a (add b c)) )
  (pow_mul: forall a b c : R, (mul (pow a b) (pow a c)) = (pow a (add b c)) )
  (pow_one: forall a : R, (pow a one) = a )
  (pow_two: forall a : R, (pow a two) = (mul a a) )
  (pow_three: forall a : R, (pow a three) = (mul a (pow a two)) )
  (pow_four: forall a : R, (pow a four) = (mul (pow a two) (pow a two)) )
  (one_pow: forall a : R, a = (pow a one) )
  (two_pow: forall a : R, (mul a a) = (pow a two) )
  (three_pow: forall a : R, (mul a (pow a two)) = (pow a three) )
  (four_pow: forall a : R, (mul (pow a two) (pow a two)) = (pow a four) )
  (two_add : forall a : R, (add a a) = (mul two a) )
  (add_two : forall a : R, (mul two a) = (add a a) )
  (char_two : forall a : R, (add a a) = zero )
  (x y : R)
  : ((x + y)^three) = add (((x^three) + (x*(y^two))) + ((x^two)*y)) (y^three) := by

    timed calc (x + y)^three
    -- _ = (x + y) * (x + y) * (x + y)                                := by ges3
    _ = (x + y) * ((x * (x + y)) + (y * (x + y)))                   := by ges3
    -- _ = (x + y) * ((((x^two) + (x * y)) + (y * x)) + (y^two))       := by ges3
    -- _ = (x + y) * ((x^two) + (y^two))                               := by ges3
    -- _ = add (x * ((x^two) + (y^two))) (y * ((x^two) + (y^two)))    := by ges3
    -- _ = add (((x * (x^two)) + (x*(y^two))) + (y * (x^two))) (y*(y^two)) := by ges3
    _ = add (((x^three) + x*(y^two)) + (x^two)*y) (y^three)             := by ges3
