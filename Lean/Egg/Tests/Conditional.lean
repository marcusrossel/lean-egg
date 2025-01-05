import Egg

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
example (h : x ∧ y → 1 = 2) : 1 = 2 := by
  egg [h]

example (h₁ : x ∧ y) (h₂ : x ∧ y → 1 = 2) : 1 = 2 := by
  egg [h₂; h₁]

example (h₁ : x ∧ y) (h₂ : x ∧ y → 1 = 2) : 1 = 2 := by
  egg [*; *]

example (h₁ : x ∧ y) (h₂ : y ∧ x → 1 = 2) : 1 = 2 := by
  egg [h₂; and_comm.mp h₁]

example (h₁ : x ∧ y) (h₂ : y ∧ x → 1 = 2) : 1 = 2 := by
  have h₁' := and_comm.mp h₁
  egg [h₂; h₁']

example (h₁ : x ∧ y) (h₂ : y ∧ x → 1 = 2) : 1 = 2 := by
  have := and_comm.mp h₁
  egg [*; *]

example (h₁ : ∀ n, n > 2 → n = x) (h₂ : 3 > 2) : 3 = x := by
  egg [h₁; h₂]

-- This tests that we can handle multiple conditions.
example (h₁ : ∀ n, n > 2 → n > 3 → n = x) (h₂ : 4 > 2) (h₃ : 4 > 3) : 4 = x := by
  egg [h₁; h₂, h₃]

-- This tests that conditions and facts do not need to be in order for proof reconstruction to work.
example (h₁ : ∀ n, n > 2 → n > 3 → n = x) (h₃ : 4 > 3) (h₂ : 4 > 2) : 4 = x := by
  egg [h₁; h₂, h₃]

example {a : Nat} (h : a < b) : a % b = a := by
  egg [Nat.mod_eq_of_lt; h]

-- This test, and the following two, check that adding redundant rewrites and changing their order
-- does not affect the outcome of the tactic.
example {x : Nat} (h₁ : x = y) (h₂ : x = y → 1 = 2) : 1 = 2 := by
  egg [h₂; h₁]

example {x : Nat} (h₁ : x = y) (h₂ : x = y → 1 = 2) : 1 = 2 := by
  egg [h₂, h₁; h₁]

example {x : Nat} (h₁ : x = y) (h₂ : x = y → 1 = 2) : 1 = 2 := by
  egg [h₁, h₂; h₁]

example (h₁ : ∀ p, p ∧ p) (h₂ : (∀ p, p ∧ p) → q = True) : q = True := by
  egg [h₂; h₁]

/-- error: Rewrite #0 requires condition of type 'Prop' which is neither a proof nor an instance. -/
#guard_msgs in
example (h₁ : Prop) (h₂ : ∀ p : Prop, p → 1 = id 1) : 1 = id 1 := by
  egg [h₂; h₁]

class Fix (α : Type) where
  fix : ∀ (f : α → α) (a : α), f a = a

-- Note: `Fix.fix` used to be invalid as a rewrite as it contained an "unbounded condition" as `α`
--       is not specified in `f a` or `a`, but is required for `Fix α`. Currently, this proof only
--       succeeds because of type class specialization for conditions. That is, the `Fix α`
--       condition is specialized before eqsat. In the future, this should also work with
--       `egg.genTcSpecs false`, as type class instance conditions should be satisfied by synthesis.
example [inst : Fix Nat] (f : Nat → Nat) (a : Nat) : f a = a := by
  egg [Fix.fix]

-- This test checks that rewriting of facts is handled correctly.
example {p q r : Prop} (h₁ : p) (h₂ : p ↔ q) (h₃ : q → (p ↔ r)) : p ↔ r := by
  egg [h₂, h₃; h₁]

-- This test checks that multiple rewriting of facts is handled correctly.
example {p q r : Prop} (h₁ : p) (h₂ : p ↔ q) (h₃ : q ↔ r) (h₄ : r → (p ↔ s)) : p ↔ s := by
  egg [h₂, h₃, h₄; h₁]
