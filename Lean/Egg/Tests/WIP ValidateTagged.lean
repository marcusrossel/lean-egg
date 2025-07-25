import Egg

class Group (α) extends Mul α, One α, Inv α where
  mul_assoc     (a b c : α) : (a * b) * c = a * (b * c)
  one_mul       (a : α)     : 1 * a = a
  mul_one       (a : α)     : a * 1 = a
  inv_mul_self  (a : α)     : a⁻¹ * a = 1
  mul_inv_self  (a : α)     : a * a⁻¹ = 1

variable [Group α] (a b x y : α)

attribute [egg group] Group.mul_assoc
attribute [egg group] Group.one_mul
attribute [egg group] Group.mul_one
attribute [egg group] Group.inv_mul_self
attribute [egg group] Group.mul_inv_self

def hPow : α → Nat → α
    | _, 0 => 1
    | a, (n+1) => a * hPow a n

instance [Group α] : HPow α Nat α := ⟨hPow⟩

def OrderN (n : Nat) (a : α) : Prop := a^n = 1

-- not defining the cardinality here for space reasons
def card (α) [Group α] : Nat := sorry

-- This one should not go through! not an equality
@[egg order]
theorem ex_min_order : ∃ n : Nat, OrderN n a ∧ (∀ n', n' < n → ¬ OrderN n a) := sorry

-- This should also be recognized as an equality
@[egg order]
theorem card_order : OrderN (card α) a := by
  sorry

def Abelian (α) [Group α] : Prop := ∀ a b : α, a * b = b * a

def commutator := a*b*a⁻¹*b⁻¹

-- Ideally, egg can see through this prop that there's an equality?
@[egg abel]
theorem all_commutators_trivial_abelian : (∀ a b : α, commutator a b = 1) → Abelian α := by sorry

/-- We should not break egg after adding these lemmas -/
example : a * b = b * a := by
  egg
