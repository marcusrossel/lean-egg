import Egg

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

variable (G : Type) [Magma G]

abbrev Equation387  := ∀ (x y : G), x ◇ y = (y ◇ y) ◇ x
abbrev Equation43   := ∀ (x y : G), x ◇ y = y ◇ x
abbrev Equation2    := ∀ (x y : G), x = y
abbrev Equation1689 := ∀ (x y z : G), x = (y ◇ x) ◇ ((x ◇ z) ◇ z)

theorem Equation387_implies_Equation43 (h : Equation387 G) : Equation43 G := by
  egg [*]

set_option egg.explosion true in
theorem Equation1571_implies_Equation40 (h : ∀ (x y z : G), x = (y ◇ z) ◇ (y ◇ (x ◇ z))) :
    ∀ (x y : G), x ◇ x = y ◇ y := by
  egg [*]

set_option egg.explosion true in
theorem Equation3744_implies_Equation381 (h : ∀ (x y z w : G), x ◇ y = (x ◇ z) ◇ (w ◇ y)) :
    ∀ (x y z : G), x ◇ y = (x ◇ z) ◇ y := by
  egg [*]

set_option egg.explosion true in
theorem Equation1689_implies_Equation2' (h : Equation1689 G) : Equation2 G := by
  have : ∀ a b c : G, a ◇ (b ◇ ((b ◇ c) ◇ c)) = (a ◇ b) ◇ b := by egg [*, h _ (_ ◇ _) _; h]
  egg [*]

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
