import Egg

class One (α) where one : α
instance [One α] : OfNat α 1 where ofNat := One.one

class Inv (α) where inv : α → α
postfix:max "⁻¹" => Inv.inv

class Group (α) extends Mul α, One α, Inv α where
  mul_assoc     (a b c : α) : (a * b) * c = a * (b * c)
  one_mul       (a : α)     : 1 * a = a
  mul_one       (a : α)     : a * 1 = a
  inv_mul_self  (a : α)     : a⁻¹ * a = 1
  mul_inv_self  (a : α)     : a * a⁻¹ = 1

variable [Group α] (a b x y : α)

attribute [egg] Group.mul_assoc
attribute [egg] Group.one_mul
attribute [egg] Group.mul_one
attribute [egg] Group.inv_mul_self
attribute [egg] Group.mul_inv_self


@[egg]
theorem inv_mul_cancel_left : a⁻¹ * (a * b) = b := by
  egg

#show_egg_set

@[egg]
theorem mul_inv_cancel_left : a * (a⁻¹ * b) = b :=  by
  egg

@[egg]
theorem group_cancel : (∀ a : α, a * b = a) → a = 1 := by
  intros h
  egg [h]

@[egg]
lemma mul_eq_de_eq_inv_mul : x = a⁻¹ * y → a * x = y := by
 egg

def hPow : α → Nat → α
    | _, 0 => 1
    | a, (n+1) => a * hPow a n

instance [Group α] : HPow α Nat α := ⟨hPow⟩

def OrderN (n : Nat) (a : α) : Prop := a^n = 1

-- not defining the cardinality here for space reasons
def card (α) [Group α] : Nat := sorry

-- This one should not go through! not an equality
@[egg]
theorem ex_min_order : ∃ n : Nat, OrderN n a ∧ (∀ n', n' < n → ¬ OrderN n a) := sorry

-- This should also be recognized as an equality
@[egg]
theorem card_order : OrderN (card α) a := by
  sorry

def Abelian (α) [Group α] : Prop := ∀ a b : α, a * b = b * a

def commutator := a*b*a⁻¹*b⁻¹

-- Ideally, egg can see through this prop that there's an equality?
@[egg]
theorem all_commutators_trivial_abelian : (∀ a b : α, commutator a b = 1) → Abelian α := by sorry
