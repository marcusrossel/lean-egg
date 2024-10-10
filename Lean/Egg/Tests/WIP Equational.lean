import Egg

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

variable (G : Type) [Magma G]

abbrev Equation387 := ∀ (x y : G), x ◇ y = (y ◇ y) ◇ x
abbrev Equation43  := ∀ (x y : G), x ◇ y = y ◇ x

theorem Equation387_implies_Equation43_calc (h : Equation387 G) : Equation43 G := by
  intro x y
  egg calc [*]
    x ◇ y
    _ = (y ◇ y) ◇ x
    _ = (x ◇ x) ◇ (y ◇ y)
    _ = ((y ◇ y) ◇ (y ◇ y)) ◇ (x ◇ x)
    _ = ((y ◇ y) ◇ y) ◇ (x ◇ x)
    _ = (y ◇ y) ◇ (x ◇ x)
    _ = (x ◇ x) ◇ y
    _ = y ◇ x

set_option egg.explosion true in
theorem Equation1571_implies_Equation40' (h : ∀ (x y z : G), x = (y ◇ z) ◇ (y ◇ (x ◇ z))) :
    ∀ (x y : G), x ◇ x = y ◇ y := by
  sorry -- egg [*]
