import Egg

axiom R : Type
axiom R.add : R → R → R
axiom R.sub : R → R → R
axiom R.mul : R → R → R
axiom R.div : R → R → R
axiom R.pow : R → Nat → R
axiom R.zero : R
axiom R.one : R
axiom R.inv : R → R
axiom R.neg : R → R
axiom R.choose : R → R → R
axiom R.factorial : R → R

noncomputable instance : OfNat R 0 where ofNat := R.zero
noncomputable instance : OfNat R 1 where ofNat := R.one
noncomputable instance : Add R     where add   := R.add
noncomputable instance : Sub R     where sub   := R.sub
noncomputable instance : Mul R     where mul   := R.mul
noncomputable instance : Div R     where div   := R.div
noncomputable instance : Pow R Nat where pow   := R.pow
notation:10000 n "!" => R.factorial n

open Egg.Guides Egg.Config.Modifier in
set_option hygiene false in
macro "rot" mod:egg_cfg_mod base:(egg_base)? guides:(egg_guides)? : tactic => `(tactic|
  egg $mod [comm_add, comm_mul, add_assoc, mul_assoc, sub_canon, sub_cancel, sub_add_assoc, neg_add,
  neg_neg, neg_one_mul, sub_add, div_canon, zero_add, zero_mul, mul_div_assoc, add_fractions,
  mul_fractions, one_mul, distribute, factor_div, factorial_case, factorial_case2, factorial_one,
  factorial_zero, binomial_helper, inductive_hypothesis] $[$base]? $[$guides]?
)

open R

example
    (comm_add : ∀ a b : R,  a + b = b + a)
    (comm_mul:  ∀ a b : R, a * b = b * a)
    (add_assoc: ∀ a b c : R, a + (b + c) = (a + b) + c)
    (mul_assoc: ∀ a b c : R, a * (b * c) = (a * b) * c)
    (sub_canon: ∀ a b : R, (a - b)  = a + ((R.neg 1) * b))
    (sub_cancel : ∀ a : R, a - a = 0)
    (sub_add_assoc : ∀ a b c : R, a + (b - c) = (a + b) - c)
    (neg_add : ∀ a : R , a + (R.neg a) = 0)
    (neg_neg : ∀ a : R, (R.neg (R.neg a)) = a)
    (neg_one_mul : ∀ a : R, (R.neg 1) * a = R.neg a)
    (sub_add : ∀ a b c : R, a - (b - c) = a - b + c)
    (div_canon : ∀ a b : R, (a / b) = a * (R.inv b))
    (zero_add: ∀ a : R, a + 0 = a )
    (zero_mul: ∀ a : R, a * 0 = 0)
    (mul_div_assoc : ∀ a b c : R, a * (b / c) = (a * b) / c)
    (add_fractions : ∀ a b c d : R, (a / b) + (c / d) = (a * d + b * c) / (b * d))
    (mul_fractions : ∀ a b c d : R , (a / b) * (c / d) = (a * c) / (b * d))
    (one_mul: ∀ a : R,  a * 1 = a)
    (distribute: ∀ a b c : R, a * (b + c)  = (a * b) + (a * c))
    (factor_div : ∀ a b c d e f: R , (a / b) * (c/d + e/f) = (a * c) / (b * d) + (a * e) / (b * f))
    (factorial_case : ∀ n : R, (n)! =  n * (n - 1)!)
    (factorial_case2 : ∀ n : R, (n + 1)! = (n + 1) * (n!))
    (factorial_one : ∀ n : R, (1)! = 1 )
    (factorial_zero : ∀ n : R, (0)! = 1)
    (binomial_helper : ∀ n r : R, (choose (n + 1) r) = ((choose n (r - 1)) + (choose n r)))
    (n : R)
    (inductive_hypothesis : ∀ r : R, (choose n r) = (n)! / ((r)! * (n - r)!))
    (r : R) :
    (choose (n + 1) r) =  (n + 1)! / (r ! * (n + 1 - r)!) := by
  calc (choose (n + 1) r)
    _ = choose n (r - 1) + choose n r                                         := by rot
    _ = (n !) / ((r - 1)! * (n - r + 1)!) + (n !) / (r ! * (n - r)!)          := by rot
    _ = (n !) / ((r - 1)! * (n - r)!) * (1 / (n - r + 1) + 1 / r)             := by rot
    _ = (n !) / ((r - 1)! * (n - r)!) * ((r + n - r + 1) / (r * (n - r + 1))) := by rot
    _ = (n !) / ((r - 1)! * (n - r)!) * ((n + 1) / (r * (n - r + 1)))         := by sorry
    _ = (n + 1)! / (r ! * (n + 1 - r)!)                                       := by sorry
