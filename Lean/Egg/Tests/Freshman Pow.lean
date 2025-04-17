import Egg

class Inv (α) where inv : α → α
postfix:max "⁻¹" => Inv.inv

class One (α) where one : α
instance [One α] : OfNat α 1 where ofNat := One.one

class CommRing (α) extends Zero α, One α, Add α, Sub α, Mul α, Div α, Pow α Nat, Inv α, Neg α where
  comm_add  (a b : α)   : a + b = b + a
  comm_mul  (a b : α)   : a * b = b * a
  add_assoc (a b c : α) : a + (b + c) = (a + b) + c
  mul_assoc (a b c : α) : a * (b * c) = (a * b) * c
  sub_canon (a b : α)   : a - b = a + -b
  neg_add   (a : α)     : a + -a = 0
  div_canon (a b : α)   : a / b = a * b⁻¹
  zero_add  (a : α)     : a + 0 = a
  zero_mul  (a : α)     : a * 0 = 0
  one_mul   (a : α)     : a * 1 = a
  distrib   (a b c : α) : a * (b + c) = (a * b) + (a * c)
  pow_zero  (a : α)     : a ^ 0 = 1
  pow_succ  (a : α)     : a ^ (n + 1) = a * (a ^ n)

class CharTwoRing (α) extends CommRing α where
  char_two (a : α) : a + a = 0

open CommRing CharTwoRing Egg.Guides Egg.Config.Modifier in
macro "char_two_ring" baskets:ident* mod:egg_cfg_mod guides:(egg_guides)? : tactic => `(tactic|
  egg $[$baskets]* $mod:egg_cfg_mod [comm_add, comm_mul, add_assoc, mul_assoc, sub_canon, neg_add,
  div_canon, zero_add, zero_mul, one_mul, distrib, pow_zero, pow_succ, char_two,
  Nat.succ_eq_add_one] $[$guides]?
)

variable [CharTwoRing α] (x y : α)

set_option egg.genGoalTcSpec false

theorem freshmans_dream₂ : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  calc (x + y) ^ 2
    _ = (x + y) * (x + y)             := by char_two_ring
    _ = x * (x + y) + y * (x + y)     := by char_two_ring
    -- _ = x ^ 2 + x * y + y * x + y ^ 2 := by char_two_ring
    _ = x ^ 2 + y ^ 2                 := by char_two_ring

theorem freshmans_dream₂' : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  char_two_ring

theorem freshmans_dream₃ : (x + y) ^ 3 = x ^ 3 + x * y ^ 2 + x ^ 2 * y + y ^ 3 := by
  calc (x + y) ^ 3
    _ = (x + y) * (x + y) * (x + y)                     := by char_two_ring
    _ = (x + y) * (x * (x + y) + y * (x + y))           := by char_two_ring
    _ = (x + y) * (x ^ 2 + x * y + y * x + y ^ 2)       := by char_two_ring
    _ = (x + y) * (x ^ 2 + y ^ 2)                       := by char_two_ring
    _ = x * (x ^ 2 + y ^ 2) + y * (x ^ 2 + y ^ 2)       := by char_two_ring
    _ = (x * x ^ 2) + x * y ^ 2 + y * x ^ 2 + y * y ^ 2 := by char_two_ring
    _ = x ^ 3 + x * y ^ 2 + x ^ 2 * y + y ^ 3           := by char_two_ring

-- Note: The tests below show that proof reconstruction can be the bottle neck.
--       And guides can help constructing smaller proofs.

theorem freshmans_dream₃' : (x + y) ^ 3 = x ^ 3 + x * y ^ 2 + x ^ 2 * y + y ^ 3 := by
  char_two_ring using (x + y) * (x + y)

-- TODO: Since Lean 4.10 This never completes.
--
-- This proof has about 300 steps.
--
-- set_option maxHeartbeats 300000 in
-- theorem freshmans_dream₃'' : (x + y) ^ 3 = x ^ 3 + x * y ^ 2 + x ^ 2 * y + y ^ 3 := by
--   char_two_ring
