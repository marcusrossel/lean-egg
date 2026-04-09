import Egg

set_option egg.nodeLimit 10000
set_option egg.reporting true
set_option egg.flattenReports true

-- This used to fail because explosion generation only generated explosions with up to one
-- instantiation (because of a bug).
set_option egg.explosion true

example [Mul G] (h : ∀ x y z w : G, x * y = (z * w) * w) : ∀ x y z w : G, x * y = z * w := by
  egg [h]
