import Egg

-- This demonstrates a fundamental problem with untyped rewrites.
-- We generate a rewrite of the form "?m = x", from which egg constructs an invalid explanation.

class Magma (α : Type _) where
  op : α → α → α

abbrev Equation2 (G : Type _) [Magma G] := ∀ x y : G, x = y
abbrev Equation3 (G : Type _) [Magma G] := ∀ x : G, x = Magma.op x x

set_option egg.explosion true in
theorem Equation2_implies_Equation3 (G : Type _) [Magma G] (h: Equation2 G) : Equation3 G := by
  sorry -- egg [*]
