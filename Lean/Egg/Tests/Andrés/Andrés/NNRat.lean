import Egg

-- Is this maybe what breaks egg?
section TypeStar

open Lean

/-- The syntax `variable (X Y ... Z : Sort*)` creates a new distinct implicit universe variable
for each variable in the sequence. -/
elab "Sort*" : term => do
  let u ← Lean.Meta.mkFreshLevelMVar
  Elab.Term.levelMVarToParam (.sort u)

/-- The syntax `variable (X Y ... Z : Type*)` creates a new distinct implicit universe variable
`> 0` for each variable in the sequence. -/
elab "Type*" : term => do
  let u ← Lean.Meta.mkFreshLevelMVar
  Elab.Term.levelMVarToParam (.sort (.succ u))

end TypeStar

notation "ℕ" => Nat
notation "ℤ" => Int

class AddSemigroup (G : Type u) extends Add G where
  /-- Addition is associative -/
  protected add_assoc : ∀ a b c : G, a + b + c = a + (b + c)

class MulZeroClass (M₀ : Type u) extends Mul M₀, Zero M₀ where
  /-- Zero is a left absorbing element for multiplication -/
  zero_mul : ∀ a : M₀, 0 * a = 0
  /-- Zero is a right absorbing element for multiplication -/
  mul_zero : ∀ a : M₀, a * 0 = 0

class Distrib (R : Type*) extends Mul R, Add R where
  /-- Multiplication is left distributive over addition -/
  protected left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  protected right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

class AddZeroClass (M : Type u) extends Zero M, Add M where
  /-- Zero is a left neutral element for addition -/
  protected zero_add : ∀ a : M, 0 + a = a
  /-- Zero is a right neutral element for addition -/

  protected add_zero : ∀ a : M, a + 0 = a
class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M where
  /-- Multiplication by a natural number.
  Set this to `nsmulRec` unless `Module` diamonds are possible. -/
  protected nsmul : ℕ → M → M
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  protected nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/

class AddCommMagma (G : Type u) extends Add G where
  /-- Addition is commutative in an commutative additive magma. -/
  protected add_comm : ∀ a b : G, a + b = b + a

class AddCommSemigroup (G : Type u) extends AddSemigroup G, AddCommMagma G where

class AddCommMonoid (M : Type u) extends AddMonoid M, AddCommSemigroup M
class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, Distrib α, MulZeroClass α

/-- A semigroup is a type with an associative `(*)`. -/
@[ext]
class Semigroup (G : Type u) extends Mul G where
  /-- Multiplication is associative -/
  protected mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)

class SemigroupWithZero (S₀ : Type u) extends Semigroup S₀, MulZeroClass S₀

class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α

class One (α : Type u) where
  one : α

instance (priority := 300) One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1
instance (priority := 200) One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
  one := 1

/-- Class of types that have an inversion operation. -/
class Inv (α : Type u) where
  /-- Invert an element of α. -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv.inv

/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` and `a * 1 = a` for all `a : M`. -/
class MulOneClass (M : Type u) extends One M, Mul M where
  /-- One is a left neutral element for multiplication -/
  protected one_mul : ∀ a : M, 1 * a = a
  /-- One is a right neutral element for multiplication -/
  protected mul_one : ∀ a : M, a * 1 = a

/-- A typeclass for non-associative monoids with zero elements. -/
class MulZeroOneClass (M₀ : Type u) extends MulOneClass M₀, MulZeroClass M₀

/-- The numeral `((0+1)+⋯)+1`. -/
protected def Nat.unaryCast [One R] [Zero R] [Add R] : ℕ → R
  | 0 => 0
  | n + 1 => Nat.unaryCast n + 1
/-- An `AddMonoidWithOne` is an `AddMonoid` with a `1`.
It also contains data for the unique homomorphism `ℕ → R`. -/
class AddMonoidWithOne (R : Type*) extends NatCast R, AddMonoid R, One R where
  natCast := Nat.unaryCast
  /-- The canonical map `ℕ → R` sends `0 : ℕ` to `0 : R`. -/
  natCast_zero : natCast 0 = 0 := by intros; rfl
  /-- The canonical map `ℕ → R` is a homomorphism. -/
  natCast_succ : ∀ n, natCast (n + 1) = natCast n + 1 := by intros; rfl

/-- An `AddCommMonoidWithOne` is an `AddMonoidWithOne` satisfying `a + b = b + a`. -/
class AddCommMonoidWithOne (R : Type*) extends AddMonoidWithOne R, AddCommMonoid R

/-- A unital but not-necessarily-associative semiring. -/
class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, MulZeroOneClass α,
    AddCommMonoidWithOne α

/-- The fundamental power operation in a monoid. `npowRec n a = a*a*...*a` n times.
Use instead `a ^ n`, which has better definitional behavior. -/
def npowRec [One M] [Mul M] : ℕ → M → M
  | 0, _ => 1
  | n + 1, a => npowRec n a * a

/--
An abbreviation for `npowRec` with an additional typeclass assumption on associativity
so that we can use `@[csimp]` to replace it with an implementation by repeated squaring
in compiled code.
-/
abbrev npowRecAuto {M : Type*} [Semigroup M] [One M] (k : ℕ) (m : M) : M :=
  npowRec k m

/-- The fundamental power operation in a group. `zpowRec n a = a*a*...*a` n times, for integer `n`.
Use instead `a ^ n`, which has better definitional behavior. -/
def zpowRec [One G] [Mul G] [Inv G] (npow : ℕ → G → G := npowRec) : ℤ → G → G
  | Int.ofNat n, a => npow n a
  | Int.negSucc n, a => (npow n.succ a)⁻¹

/-- A `Monoid` is a `Semigroup` with an element `1` such that `1 * a = a * 1 = a`. -/
class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
  /-- Raising to the power of a natural number. -/
  protected npow : ℕ → M → M := npowRecAuto
  /-- Raising to the power `(0 : ℕ)` gives `1`. -/
  protected npow_zero : ∀ x, npow 0 x = 1 := by intros; rfl
  /-- Raising to the power `(n + 1 : ℕ)` behaves as expected. -/
  protected npow_succ : ∀ (n : ℕ) (x), npow (n + 1) x = npow n x * x := by intros; rfl
/-- A type `M₀` is a “monoid with zero” if it is a monoid with zero element, and `0` is left
and right absorbing. -/
class MonoidWithZero (M₀ : Type u) extends Monoid M₀, MulZeroOneClass M₀, SemigroupWithZero M₀

class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α

/-- In a class equipped with instances of both `Monoid` and `Inv`, this definition records what the
default definition for `Div` would be: `a * b⁻¹`.  This is later provided as the default value for
the `Div` instance in `DivInvMonoid`.

We keep it as a separate definition rather than inlining it in `DivInvMonoid` so that the `Div`
field of individual `DivInvMonoid`s constructed using that default value will not be unfolded at
`.instance` transparency. -/
def DivInvMonoid.div' {G : Type u} [Monoid G] [Inv G] (a b : G) : G := a * b⁻¹


/-- A `DivInvMonoid` is a `Monoid` with operations `/` and `⁻¹` satisfying
`div_eq_mul_inv : ∀ a b, a / b = a * b⁻¹`.

This deduplicates the name `div_eq_mul_inv`.
The default for `div` is such that `a / b = a * b⁻¹` holds by definition.

Adding `div` as a field rather than defining `a / b := a * b⁻¹` allows us to
avoid certain classes of unification failures, for example:
Let `Foo X` be a type with a `∀ X, Div (Foo X)` instance but no
`∀ X, Inv (Foo X)`, e.g. when `Foo X` is a `EuclideanDomain`. Suppose we
also have an instance `∀ X [Cromulent X], GroupWithZero (Foo X)`. Then the
`(/)` coming from `GroupWithZero.div` cannot be definitionally equal to
the `(/)` coming from `Foo.Div`.

In the same way, adding a `zpow` field makes it possible to avoid definitional failures
in diamonds. See the definition of `Monoid` and Note [forgetful inheritance] for more
explanations on this.
-/
class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G where
  protected div := DivInvMonoid.div'
  /-- `a / b := a * b⁻¹` -/
  protected div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ := by intros; rfl
  /-- The power operation: `a ^ n = a * ··· * a`; `a ^ (-n) = a⁻¹ * ··· a⁻¹` (`n` times) -/
  protected zpow : ℤ → G → G := zpowRec npowRec
  /-- `a ^ 0 = 1` -/
  protected zpow_zero' : ∀ a : G, zpow 0 a = 1 := by intros; rfl
  /-- `a ^ (n + 1) = a ^ n * a` -/
  protected zpow_succ' (n : ℕ) (a : G) : zpow n.succ a = zpow n a * a := by
    intros; rfl
  /-- `a ^ -(n + 1) = (a ^ (n + 1))⁻¹` -/
  protected zpow_neg' (n : ℕ) (a : G) : zpow (Int.negSucc n) a = (zpow n.succ a)⁻¹ := by intros; rfl


/-- Predicate typeclass for expressing that a type is not reduced to a single element. In rings,
this is equivalent to `0 ≠ 1`. In vector spaces, this is equivalent to positive dimension. -/
class Nontrivial (α : Type*) : Prop where
  /-- In a nontrivial type, there exists a pair of distinct terms. -/
  exists_pair_ne : ∃ x y : α, x ≠ y

/-- A type `G₀` is a “group with zero” if it is a monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`.


Examples include division rings and the ordered monoids that are the
target of valuations in general valuation theory. -/
class GroupWithZero (G₀ : Type u) extends MonoidWithZero G₀, DivInvMonoid G₀, Nontrivial G₀ where
  /-- The inverse of `0` in a group with zero is `0`. -/
  protected inv_zero : (0 : G₀)⁻¹ = 0
  /-- Every nonzero element of a group with zero is invertible. -/
  protected mul_inv_cancel (a : G₀) : a ≠ 0 → a * a⁻¹ = 1

@[reducible] def Nat.Coprime (m n : Nat) : Prop := Nat.gcd m n = 1


/--
Rational numbers, implemented as a pair of integers `num / den` such that the
denominator is positive and the numerator and denominator are coprime.
-/
-- `Rat` is not tagged with the `ext` attribute, since this is more often than not undesirable
structure Rat where
  /-- Constructs a rational number from components.
  We rename the constructor to `mk'` to avoid a clash with the smart constructor. -/
  mk' ::
  /-- The numerator of the rational number is an integer. -/
  num : Int
  /-- The denominator of the rational number is a natural number. -/
  den : Nat := 1
  /-- The denominator is nonzero. -/
  den_nz : den ≠ 0 := by decide
  /-- The numerator and denominator are coprime: it is in "reduced form". -/
  reduced : num.natAbs.Coprime den := by decide
  deriving DecidableEq

@[inherit_doc] notation "ℚ" => Rat

namespace Nat
theorem coprime_one_right : ∀ n, Coprime n 1 := gcd_one_right
end Nat

namespace Rat
/-- Rational number strictly less than relation, as a `Bool`. -/
protected def blt (a b : Rat) : Bool :=
  if a.num < 0 && 0 ≤ b.num then
    true
  else if a.num = 0 then
    0 < b.num
  else if 0 < a.num && b.num ≤ 0 then
    false
  else
    -- `a` and `b` must have the same sign
   a.num * b.den < b.num * a.den
instance : LE Rat := ⟨fun a b => b.blt a = false⟩

/-- Embedding of `Int` in the rational numbers. -/
def ofInt (num : Int) : Rat := { num, reduced := Nat.coprime_one_right _ }

instance : NatCast Rat where
  natCast n := ofInt n
instance : IntCast Rat := ⟨ofInt⟩

instance : OfNat Rat n := ⟨n⟩
end Rat
/-- Nonnegative rational numbers. -/
def NNRat := {q : ℚ // 0 ≤ q}

@[inherit_doc] notation "ℚ≥0" => NNRat

/-- Typeclass for the canonical homomorphism `ℚ≥0 → K`.

This should be considered as a notation typeclass. The sole purpose of this typeclass is to be
extended by `DivisionSemiring`. -/
class NNRatCast (K : Type*) where
  /-- The canonical homomorphism `ℚ≥0 → K`.

  Do not use directly. Use the coercion instead. -/
  protected nnratCast : ℚ≥0 → K


instance NNRat.instNNRatCast : NNRatCast ℚ≥0 where nnratCast q := q

variable {K : Type*} [NNRatCast K]

/-- Canonical homomorphism from `ℚ≥0` to a division semiring `K`.

This is just the bare function in order to aid in creating instances of `DivisionSemiring`. -/
@[coe, reducible, match_pattern] protected def NNRat.cast : ℚ≥0 → K := NNRatCast.nnratCast

-- See note [coercion into rings]
instance NNRatCast.toCoeTail [NNRatCast K] : CoeTail ℚ≥0 K where coe := NNRat.cast

-- See note [coercion into rings]
instance NNRatCast.toCoeHTCT [NNRatCast K] : CoeHTCT ℚ≥0 K where coe := NNRat.cast

instance Rat.instNNRatCast : NNRatCast ℚ := ⟨Subtype.val⟩


namespace NNRat


/-- The numerator of a nonnegative rational. -/
def num (q : ℚ≥0) : ℕ := (q : ℚ).num.natAbs

/-- The denominator of a nonnegative rational. -/
def den (q : ℚ≥0) : ℕ := (q : ℚ).den

/-- The default definition of the coercion `ℚ≥0 → K` for a division semiring `K`.

`↑q : K` is defined as `(q.num : K) / (q.den : K)`.

Do not use this directly (instances of `DivisionSemiring` are allowed to override that default for
better definitional properties). Instead, use the coercion. -/
def castRec [NatCast K] [Div K] (q : ℚ≥0) : K := q.num / q.den
end NNRat

class DivisionSemiring (K : Type*) extends Semiring K, GroupWithZero K, NNRatCast K where
  protected nnratCast := NNRat.castRec


def Function.Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

class CharZero (R) [AddMonoidWithOne R] : Prop where
  /-- An additive monoid with one has characteristic zero if the canonical map `ℕ → R` is
  injective. -/
  cast_injective : Function.Injective (Nat.cast : ℕ → R)

/--
The notation typeclass for heterogeneous additive actions.
This enables the notation `a +ᵥ b : γ` where `a : α`, `b : β`.
-/
class HVAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a +ᵥ b` computes the sum of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hVAdd : α → β → γ

/--
The notation typeclass for heterogeneous scalar multiplication.
This enables the notation `a • b : γ` where `a : α`, `b : β`.

It is assumed to represent a left action in some sense.
The notation `a • b` is augmented with a macro (below) to have it elaborate as a left action.
Only the `b` argument participates in the elaboration algorithm: the algorithm uses the type of `b`
when calculating the type of the surrounding arithmetic expression
and it tries to insert coercions into `b` to get some `b'`
such that `a • b'` has the same type as `b'`.
See the module documentation near the macro for more details.
-/
class HSMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a • b` computes the product of `a` and `b`.
  The meaning of this notation is type-dependent, but it is intended to be used for left actions. -/
  hSMul : α → β → γ

/-- Type class for the `+ᵥ` notation. -/
class VAdd (G : Type u) (P : Type v) where
  /-- `a +ᵥ b` computes the sum of `a` and `b`. The meaning of this notation is type-dependent,
  but it is intended to be used for left actions. -/
  vadd : G → P → P

/-- Type class for the `-ᵥ` notation. -/
class VSub (G : outParam Type*) (P : Type*) where
  /-- `a -ᵥ b` computes the difference of `a` and `b`. The meaning of this notation is
  type-dependent, but it is intended to be used for additive torsors. -/
  vsub : P → P → G

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
class SMul (M : Type u) (α : Type v) where
  /-- `a • b` computes the product of `a` and `b`. The meaning of this notation is type-dependent,
  but it is intended to be used for left actions. -/
  smul : M → α → α

@[inherit_doc] infixl:65 " +ᵥ " => HVAdd.hVAdd
@[inherit_doc] infixl:65 " -ᵥ " => VSub.vsub
@[inherit_doc] infixr:73 " • " => HSMul.hSMul

instance instHSMul {α β} [SMul α β] : HSMul α β β where
  hSMul := SMul.smul


/-- Typeclass for multiplicative actions by monoids. This generalizes group actions. -/
class MulAction (α : Type*) (β : Type*) [Monoid α] extends SMul α β where
  /-- One is the neutral element for `•` -/
  protected one_smul : ∀ b : β, (1 : α) • b = b
  /-- Associativity of `•` and `*` -/
  mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b

/-- Typeclass for multiplicative actions on additive structures. This generalizes group modules. -/
@[ext]
class DistribMulAction (M A : Type*) [Monoid M] [AddMonoid A] extends MulAction M A where
  /-- Multiplying `0` by a scalar gives `0` -/
  smul_zero : ∀ a : M, a • (0 : A) = 0
  /-- Scalar multiplication distributes across addition -/
  smul_add : ∀ (a : M) (x y : A), a • (x + y) = a • x + a • y

/-- A module is a generalization of vector spaces to a scalar semiring.
  It consists of a scalar semiring `R` and an additive monoid of "vectors" `M`,
  connected by a "scalar multiplication" operation `r • x : M`
  (where `r : R` and `x : M`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
@[ext]
class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends
  DistribMulAction R M where
  /-- Scalar multiplication distributes over addition from the right. -/
  protected add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  /-- Scalar multiplication by zero gives zero. -/
  protected zero_smul : ∀ x : M, (0 : R) • x = 0

@[ext]
class CommMagma (G : Type u) extends Mul G where
  /-- Multiplication is commutative in a commutative multiplicative magma. -/
  protected mul_comm : ∀ a b : G, a * b = b * a

@[ext]
class CommSemigroup (G : Type u) extends Semigroup G, CommMagma G where
class CommMonoid (M : Type u) extends Monoid M, CommSemigroup M
class CommSemiring (R : Type u) extends Semiring R, CommMonoid R

class CommMonoidWithZero (M₀ : Type*) extends CommMonoid M₀, MonoidWithZero M₀
class CommGroupWithZero (G₀ : Type*) extends CommMonoidWithZero G₀, GroupWithZero G₀

class Semifield (K : Type*) extends CommSemiring K, DivisionSemiring K, CommGroupWithZero K

instance instSemifield : Semifield ℚ≥0 := sorry

/-- A function `f : α → β` is called injective if `f x = f y` implies `x = y`. -/
def Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

/-- A function `f : α → β` is called surjective if every `b : β` is equal to `f a`
for some `a : α`. -/
def Surjective (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b

/-- A function is called bijective if it is both injective and surjective. -/
def Bijective (f : α → β) :=
  Injective f ∧ Surjective f

section GroupWithZero
variable [GroupWithZero G₀] [MulAction G₀ α] {a : G₀}

protected theorem MulAction.bijective (g : α) : Bijective (g • · : β → β) :=
  (MulAction.toPerm g).bijective

protected theorem MulAction.bijective₀ (ha : a ≠ 0) : Bijective (a • · : α → α) :=
  MulAction.bijective <| Units.mk0 a ha

protected theorem MulAction.injective₀ (ha : a ≠ 0) : Injective (a • · : α → α) :=
  (MulAction.bijective₀ ha).injective

end GroupWithZero
-- Until here it's all the background needed for the following example

variable (R S : Type*) [DivisionSemiring R] [CharZero R] [Semiring S] [Module ℚ≥0 S]

example [Module R S] (q : ℚ≥0) (a : S) : (q : R) • a = q • a := by
  refine MulAction.injective₀ (G₀ := ℚ≥0) (Nat.cast_ne_zero.2 q.den_pos.ne') ?_
  egg [
    mul_smul, den_mul_eq_num, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, smul_assoc,
    nsmul_eq_mul q.den (α := R), cast_natCast, cast_mul, den_mul_eq_num, cast_natCast,
    Nat.cast_smul_eq_nsmul
  ]
