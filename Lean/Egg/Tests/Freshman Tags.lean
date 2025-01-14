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
  pow_one   (a : α)     : a ^ 1 = a
  pow_two   (a : α)     : a ^ 2 = (a ^ 1) * a
  pow_three (a : α)     : a ^ 3 = (a ^ 2) * a

attribute [egg] CommRing.comm_add
attribute [egg] CommRing.comm_mul
attribute [egg] CommRing.add_assoc
attribute [egg] CommRing.mul_assoc
attribute [egg] CommRing.sub_canon
attribute [egg] CommRing.neg_add
attribute [egg] CommRing.div_canon
attribute [egg] CommRing.zero_add
attribute [egg] CommRing.zero_mul
attribute [egg] CommRing.one_mul
attribute [egg] CommRing.distrib
attribute [egg] CommRing.pow_zero
attribute [egg] CommRing.pow_one
attribute [egg] CommRing.pow_two
attribute [egg] CommRing.pow_three

class CharTwoRing (α) extends CommRing α where
  char_two (a : α) : a + a = 0

variable [CharTwoRing α] (x y : α)

theorem freshmans_dream₂ : (x + y) ^ 2 = (x ^ 2) + (y ^ 2) := by
  egg! calc (x + y) ^ 2
   _ = (x + y) * (x + y)
   _ = x * (x + y) + y * (x + y)
   _ = x ^ 2 + x * y + y * x + y ^ 2
   _ = x ^ 2 + y ^ 2  with [CharTwoRing.char_two]

-- TODO: Before 78480a591ed00e75435e9d0a6f64f8c8aada655e we didn't have type class rewrite gen for
--       tagged rewrites. Now that we have them, it seems that egg is overwhelmed by them.
set_option egg.genGoalTcSpec false

theorem freshmans_dream₂' : (x + y) ^ 2 = (x ^ 2) + (y ^ 2) := by
  egg! [CharTwoRing.char_two]

theorem freshmans_dream₃ : (x + y) ^ 3 = x ^ 3 + x * y ^ 2 + x ^ 2 * y + y ^ 3 := by
  egg! calc [CharTwoRing.char_two] (x + y) ^ 3
   _ = (x + y) * (x + y) * (x + y)
   _ = (x + y) * (x * (x + y) + y * (x + y))
   _ = (x + y) * (x ^ 2 + x * y + y * x + y ^ 2)
   _ = (x + y) * (x ^ 2 + y ^ 2)
   _ = x * (x ^ 2 + y ^ 2) + y * (x ^ 2 + y ^ 2)
   _ = (x * x ^ 2) + x * y ^ 2 + y * x ^ 2 + y * y ^ 2
   _ = x ^ 3 + x * y ^ 2 + x ^ 2 * y + y ^ 3

theorem freshmans_dream₃' : (x + y) ^ 3 = x ^ 3 + x * y ^ 2 + x ^ 2 * y + y ^ 3 := by
  egg! [CharTwoRing.char_two]
