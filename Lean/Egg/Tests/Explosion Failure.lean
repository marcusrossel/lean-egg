import Egg

-- This used to fail because explosion generation only generated explosions with up to one
-- instantiation (because of a bug).
set_option egg.explosion true

-- TODO: This broke when we overhauled how theorems are turned into rewrites. Looks like the problem
--       might be related to mvars not being refreshed properly?

example [Mul G] (h : ∀ x y z w : G, x * y = (z * w) * w) : ∀ x y z w : G, x * y = z * w := by
  sorry -- egg [h]
