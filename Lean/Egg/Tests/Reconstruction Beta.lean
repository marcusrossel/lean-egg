import Egg

-- BUG: This started causing issues when we moved to small-step β-reduction (perhaps because then
--      β-reduction actually started working). Turning off β-reduction fixes the problem.
set_option egg.eraseProofs false in
set_option egg.genBetaRw true in
example (arr : Array α) (i : Nat) (h₁ h₂ : i < arr.size) : arr[i]'h₁ = arr[i]'h₂ := by
  sorry-- egg
