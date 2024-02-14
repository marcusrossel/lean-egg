import Egg

-- TODO: This set of test cases seems to demonstrate that `typeTags ≠ .none` is way too slow or
--       doesn't work.

class Group (α) where
  zero          : α
  neg           : α → α
  add           : α → α → α
  add_assoc     : ∀ a b c, add (add a b) c = add a (add b c)
  zero_add      : ∀ a, add zero a = a
  add_zero      : ∀ a, add a zero = a
  add_left_inv  : ∀ a, add (neg a) a = zero
  add_right_inv : ∀ a, add a (neg a) = zero

open Group

instance [Group α] : Neg α where neg := neg
instance [Group α] : Add α where add := add
instance [Group α] : OfNat α 0 where ofNat := zero

variable [g : Group G] {a b c : G}

-- NOTE: Using `@add_assoc` etc, produces `.proj` expressions.

-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/elabTerm.20with.20TC

theorem t [Add α] (a b : α) : a + b = b + a :=
  sorry

set_option trace.egg true

-- TODO: This example shows that we're not treating level params correctly, as they're hindering the
--       rewriting. Can we replace all universe params by mvars such that the same param maps to the
--       same mvar in all rewrites?
example {a b : Nat} : a + b = b + a := by
  egg [t]

theorem inv_add_cancel_left'' : add (neg a) (add a b) = b := by
  rw [←add_assoc]
  rw [add_left_inv]
  rw [zero_add]

open Lean Meta Elab Term in
#eval do
  let e ← elabTerm (← `(t)) none
  let ty ← inferType e
  IO.println ty

-- BUG: "type expected g"
theorem inv_add_cancel_left' : -a + (a + b) = add (neg a) (add a b) := by
  egg [@add_assoc, @zero_add, @add_zero, @add_left_inv, @add_right_inv]

theorem inv_add_cancel_left : -a + (a + b) = b := by
  egg [@add_assoc, @zero_add, @add_zero, @add_left_inv, @add_right_inv]

theorem add_inv_cancel_left : a + (-a + b) = b := by
  egg [add_assoc, zero_add, add_zero, add_left_inv, add_right_inv]

theorem inv_add : -(a + b) = -b + -a := by
  egg [add_assoc, zero_add, add_zero, add_left_inv, add_right_inv]

theorem zero_inv : -(0 : G) = 0 := by
  egg [add_assoc, zero_add, add_zero, add_left_inv, add_right_inv]

theorem inv_inv : -(-a) = a := by
  egg [add_assoc, zero_add, add_zero, add_left_inv, add_right_inv]
