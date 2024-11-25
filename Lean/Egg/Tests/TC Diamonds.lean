-- Inspired by: Wieser, Eric. "Multiple-inheritance hazards in dependently-typed algebraic hierarchies." International Conference on Intelligent Computer Mathematics. Cham: Springer Nature Switzerland, 2023.
import Egg

namespace Nested

class AddCommMonoid (α : Type _) where
  add : α → α → α
  zero : α
  add_zero : ∀ a : α, add a zero = a
  zero_add : ∀ a : α, add zero a = a
  add_comm : ∀ a b : α, add a b = add b a

class AddCommGroup (α : Type _) extends AddCommMonoid α where
  neg : α → α
  add_neg : ∀ a : α, add (neg a) a = zero
  neg_add : ∀ a : α, add a (neg a) = zero

class Semiring (α : Type _) extends AddCommMonoid α where
  mul : α → α → α
  mul_assoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)
  one : α
  mul_one : ∀ a : α, mul a one = a
  one_mul : ∀ a : α, mul one a = a
  left_distrib : ∀ a b c : α, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c : α, mul (add a b) c = add (mul a c) (mul b c)
  zero_mul : ∀ a : α, mul zero a = zero
  mul_zero : ∀ a : α, mul a zero = zero

class Ring (α : Type _) extends Semiring α, AddCommGroup α where

attribute [egg] AddCommMonoid.add_zero
attribute [egg] AddCommMonoid.zero_add
attribute [egg] AddCommMonoid.add_comm
attribute [egg] AddCommGroup.add_neg
attribute [egg] AddCommGroup.neg_add
attribute [egg] Semiring.mul_assoc
attribute [egg] Semiring.mul_one
attribute [egg] Semiring.one_mul
attribute [egg] Semiring.left_distrib
attribute [egg] Semiring.right_distrib
attribute [egg] Semiring.zero_mul
attribute [egg] Semiring.mul_zero

open AddCommMonoid AddCommGroup Semiring Ring

infixl:65 (priority := high) " + " => add
infixl:65 (priority := high) " * " => mul

theorem test [Ring α] (a b : α) : a + b = b + a := by
  egg!
/--
error: egg failed to prove the goal (reached time limit)
-/
#guard_msgs in
theorem combine_classes [Ring α] (a b c : α) (h : b + c = one) : (a + (b + Ring.neg b)) * (b + c) = a := by
 egg! [h]

end Nested

namespace Flat


class Ring (α : Type _) where
  add : α → α → α
  zero : α
  add_zero : ∀ a : α, add a zero = a
  zero_add : ∀ a : α, add zero a = a
  add_comm : ∀ a b : α, add a b = add b a
  mul : α → α → α
  mul_assoc : ∀ a b c : α, mul (mul a b) c = mul a (mul b c)
  one : α
  mul_one : ∀ a : α, mul a one = a
  one_mul : ∀ a : α, mul one a = a
  left_distrib : ∀ a b c : α, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c : α, mul (add a b) c = add (mul a c) (mul b c)
  zero_mul : ∀ a : α, mul zero a = zero
  mul_zero : ∀ a : α, mul a zero = zero
  neg : α → α
  add_neg : ∀ a : α, add (neg a) a = zero
  neg_add : ∀ a : α, add a (neg a) = zero

attribute [egg] Ring.add_zero
attribute [egg] Ring.zero_add
attribute [egg] Ring.add_comm
attribute [egg] Ring.add_neg
attribute [egg] Ring.neg_add
attribute [egg] Ring.mul_assoc
attribute [egg] Ring.mul_one
attribute [egg] Ring.one_mul
attribute [egg] Ring.left_distrib
attribute [egg] Ring.right_distrib
attribute [egg] Ring.zero_mul
attribute [egg] Ring.mul_zero

open Ring

infixl:65 (priority := high) " + " => add
prefix:65 (priority := high) " - " => neg
infixl:65 (priority := high) " * " => mul

theorem test [Ring α] (a b : α) : a + b = b + a := by
  egg!

theorem combine_classes [Ring α] (a b c : α) (h : b + c = one) : (a + (b + neg b)) * (b + c) = a := by
 egg! [h]

end Flat
