import Egg

-- Tests for manually inspecting what terms look like with the `reduce` option.
set_option trace.egg true

example (a : Nat) (h : ∀ x : Nat, x + 1 = 1 + x) : a + 1 = 1 + a := by
  egg (config := { reduce := true }) [h]
