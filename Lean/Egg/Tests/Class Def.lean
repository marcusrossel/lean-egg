import Egg
import Lean
open Lean Meta Elab Term Tactic

def Mul.pow [Mul α] [OfNat α 1] (a : α) : Nat → α
  | 0     => 1
  | n + 1 => a * (pow a n)

instance mulPow [Mul α] [OfNat α 1] : Pow α Nat where
  pow := Mul.pow

-- TODO: For some reason the rewrites for `Mul.pow` instantiate `α` to `Nat`.
set_option pp.explicit true in
set_option trace.egg true in
example [Mul α] [OfNat α 1] (a : α) : Mul.pow a 0 = (1 : α) := by
  sorry -- egg [Mul.pow]

-- example [Mul α] [OfNat α 1] (a : α) : a ^ 0 = (1 : α) := by
--   egg [Mul.pow]
