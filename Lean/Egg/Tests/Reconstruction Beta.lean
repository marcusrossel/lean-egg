import Egg

-- This once started causing issues when we moved to small-step β-reduction (perhaps because then
-- β-reduction actually started working). Turning off β-reduction fixed the problem in that case.
-- Now it just seems to work.
example (arr : Array α) (i : Nat) (h₁ h₂ : i < arr.size) : arr[i]'h₁ = arr[i]'h₂ := by
  egg
