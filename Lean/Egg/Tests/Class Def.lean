import Egg
import Lean
open Lean Meta Elab Term Tactic

def Mul.pow [Mul α] [OfNat α 1] (a : α) : Nat → α
  | 0     => 1
  | n + 1 => a * (pow a n)

instance mulPow [Mul α] [OfNat α 1] : Pow α Nat where
  pow := Mul.pow

example [Mul α] [OfNat α 1] (a : α) : Mul.pow a 0 = (1 : α) := by
  egg [Mul.pow]

example [Mul α] [OfNat α 1] (a : α) : a ^ 0 = (1 : α) := by
  egg [Mul.pow]
