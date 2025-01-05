import Egg

example (h : 0 = 0 → 1 = 2) : 1 = 2 := by
  egg [h]

example (h : (0 = (fun x => x) 0) → 1 = 2) : 1 = 2 := by
  egg [h]

variable {x : Nat} {f : Nat → Nat}

example (h₁ : x = y) (h₂ : x = y → 1 = 2) : 1 = 2 := by
  egg [h₁, h₂]

example (h₁ : x = y) (h₂ : x = y → 1 = 2) : 1 = 2 := by
  egg [h₁, h₂]

example (h₁ : x = y) (h₂ : y = z) (h₃ : x = z → 1 = 2) : 1 = 2 := by
  egg [h₁, h₂, h₃]

-- Note: The fact that this works is kind of accidental. By default, we shouldn't expect this to
--       work, because the goal doesn't introduce `x` into the e-graph, so we shouldn't be able to
--       establish `f x = x` by rewriting with `h₁`. But when the applier for `h₂` is run, in order
--       to check the precondition, we need to find the e-classes of `f x` and `x`. To do this, we
--       use `add_instantiation` which also adds `f x` and `x` to the e-graph (in fact, we also add
--       the term `f x = x` to the e-graph). Thus, after `h₂` fails, we can actually apply `h₁`
--       which then enables `h₂` to succeed.
example (h₁ : ∀ a : Nat, f a = a) (h₂ : f x = x → 1 = 2) : 1 = 2 := by
  egg [h₁, h₂]

example (h₁ : ∀ a : Nat, f a = a) (h₂ : p ∧ q) (h₃ : (f x = x) → (p ∧ q) → 1 = 2) : 1 = 2 := by
  egg [h₁, h₂, h₃]

example (h₁ : ∀ a : Nat, f a = a) (h₂ : p ∧ q) (h₃ : p ∧ q ↔ r) (h₄ : (f x = x) → r → 1 = 2) :
    1 = 2 := by
  egg [h₁, h₂, h₃, h₄]
