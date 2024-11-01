import Egg

/- TODO: Why is proof reconstruction failing here? The explanation seems totally fine:

  (app (app (λ (const Nat) (app f (bvar 0))) y) y)
  (app (app (Rewrite=> ≡η f) y) y)
  (app (Rewrite=> #0 g) y)
  (Rewrite<= #1-rev (app (app i y) (lit 0)))
  (app (app (Rewrite<= ≡η (λ (const Nat) (app i (bvar 0)))) y) (lit 0))

Even stranger, if you flip the LHS and RHS of the goal, it suddenly works. The produced explanation
in that case is the same just backwards. So a hacky fix would be to always obtain explanations from
egg in both directions and if one fails try the other.
-/
set_option egg.retryWithShapes false in
example (f i : Nat → Nat → Nat) (h₁ : f y = g) (h₂ : g y = i y (nat_lit 0)) :
    (f ·) y y = (i ·) y (nat_lit 0) := by
  sorry -- egg [h₁, h₂]
