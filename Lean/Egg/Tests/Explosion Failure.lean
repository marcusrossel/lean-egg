import Egg

-- This used to fail because explosion generation only generated explosions with up to one
-- instantiation (because of a bug).
set_option egg.explosion true

example [Mul G] (h : ∀ x y z w : G, x * y = (z * w) * w) : ∀ x y z w : G, x * y = z * w := by
  egg [h]
