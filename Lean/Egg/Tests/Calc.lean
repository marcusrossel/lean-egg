import Egg

example : 0 = 0 := by
  egg calc 0 = 0

example : 0 = 0 := by
  egg calc _ = 0

example : 0 = 0 := by
  egg calc 0
    _ = 0

example : 0 = 0 := by
  egg calc _ = _

example (h : a = b) : a = b := by
  egg calc [h] _ = _

example (h₁ : a = b) (h₂ : b = c) : a = c := by
  egg calc [h₁, h₂]
    a = b
    _ = c

example : ∀ a b c : Nat, (a = b) → (b = c) → a = c := by
  intro a b c h₁ h₂
  egg calc [h₁, h₂]
    a = b
    _ = c

example (h₁ : a = b) (h₂ : b = c) : a = c := by
  egg calc
    a = b with [h₁]
    _ = c with [h₂]

set_option trace.egg true in
example (h₁ : 0 = 0 → a = b) : a = b := by
  egg calc [h₁, (rfl : 0 = 0)]
    _ = _

example (h₁ : 0 = 0 → a = b) : a = b := by
  egg calc [h₁]
    _ = _ with [(rfl : 0 = 0)]
