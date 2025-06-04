import Egg

-- Inspired by:
-- Wieser, Eric. "Multiple-inheritance hazards in dependently-typed algebraic hierarchies."
-- International Conference on Intelligent Computer Mathematics.
-- Cham: Springer Nature Switzerland, 2023.

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

attribute [egg ring] AddCommMonoid.add_zero
attribute [egg ring] AddCommMonoid.zero_add
attribute [egg ring] AddCommMonoid.add_comm
attribute [egg ring] AddCommGroup.add_neg
attribute [egg ring] AddCommGroup.neg_add
attribute [egg ring] Semiring.mul_assoc
attribute [egg ring] Semiring.mul_one
attribute [egg ring] Semiring.one_mul
attribute [egg ring] Semiring.left_distrib
attribute [egg ring] Semiring.right_distrib
attribute [egg ring] Semiring.zero_mul
attribute [egg ring] Semiring.mul_zero

open AddCommMonoid AddCommGroup Semiring Ring

infixl:65 (priority := high) " + " => add
infixl:70 (priority := high) " * " => mul
prefix:75 (priority := high) "-"   => Ring.neg

theorem test [Ring α] (a b : α) : a + b = b + a := by
  egg +ring

theorem just_nested [Ring α] (a : α) : (a + zero) * one = a := by
  egg +ring

-- TODO: The problem here is that subtraction is `Ring.neg`, whereas the relevant theorem
--       `AddCommGroup.neg_add` is about `AddCommGroup.neg`. That is, we need a theorem like `t`.
theorem t : @Ring.neg β i = @AddCommGroup.neg β i.toAddCommGroup := rfl
--       We currently do not get this, as type class projection reductions are only generated when
--       there are no mvars in the chain of applications. But perhaps we can still reduce in that
--       case:
variable (α) (i : Ring α) in #reduce @Ring.neg α i
--       Then things work:
example [Ring α] (a : α) : add a (Ring.neg a) = zero := by
  egg [AddCommGroup.neg_add, t]
--       Alternatively, we could perform goal type specialization eagerly (not only for unlocking
--       new rewrite directions). Or perhaps we could perform goal type specialization only for the
--       purpose of enabling more type class projection reductions, but mark the unnecessarily
--       generated goal type specializations and prune them at the end.
--       Or, we could have goal type specialization during type class projection generation. That
--       is, whenever we encounter an mvar which is a type, try specializing it with the goal type.

-- TODO: See the example above.
theorem combine_classes [Ring α] (a b c : α) (h : b + c = one) : (a + (b + -b)) * (b + c) = a := by
  sorry -- egg ring [h]

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

attribute [egg ring'] Ring.add_zero
attribute [egg ring'] Ring.zero_add
attribute [egg ring'] Ring.add_comm
attribute [egg ring'] Ring.add_neg
attribute [egg ring'] Ring.neg_add
attribute [egg ring'] Ring.mul_assoc
attribute [egg ring'] Ring.mul_one
attribute [egg ring'] Ring.one_mul
attribute [egg ring'] Ring.left_distrib
attribute [egg ring'] Ring.right_distrib
attribute [egg ring'] Ring.zero_mul
attribute [egg ring'] Ring.mul_zero

open Ring

infixl:65 (priority := high) " + " => add
infixl:70 (priority := high) " * " => mul
prefix:75 (priority := high) "-"   => neg

theorem test [Ring α] (a b : α) : a + b = b + a := by
  egg +ring'

theorem just_nested [Ring α] (a : α) : (a + zero) * one = a := by
  egg +ring'

theorem combine_classes [Ring α] (a b c : α) (h : b + c = one) : (a + (b + -b)) * (b + c) = a := by
  egg +ring' [h]

end Flat
