import Egg

class Inv (α) where inv : α → α
postfix:max "⁻¹" => Inv.inv

class Zero (α) where zero : α
instance [Zero α] : OfNat α 0 where ofNat := Zero.zero

class One (α) where one : α
instance [One α] : OfNat α 1 where ofNat := One.one

class Ring (α) extends Zero α, One α, Add α, Sub α, Mul α, Div α, Pow α Nat, Inv α, Neg α where
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
  distrib   (a b c : α) : a * (b + c)  = (a * b) + (a * c)

-- TODO: How can you define factorial?
notation "(" r ")!" => r

open Ring Egg.Guides Egg.Config.Modifier in
macro "ring" mod:egg_cfg_mod base:(egg_base)? guides:(egg_guides)? : tactic => `(tactic|
  egg $mod [comm_add, comm_mul, add_assoc, mul_assoc, sub_canon, neg_add, div_canon, zero_add,
  zero_mul, one_mul, distrib] $[$base]? $[$guides]?
)
