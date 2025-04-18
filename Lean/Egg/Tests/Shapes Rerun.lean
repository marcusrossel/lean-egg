import Egg

-- Checks that we rerun with shapes when proof reconstruction fails if `egg.retryWithShapes = true`.
-- Without rerunning with shapes, the first fails during proof reconstruction with the explanation
-- shown when setting `exitPoint := some .beforeProof`.

/--
error: egg failed to build proof step 0: unification failure for LHS of rewrite #0:

  id Nat.add
vs
  ?m.264 ?m.261
in
  id Nat.add
and
  ()

• Types: ⏎
  ?m.264: Unit → Unit
  ?m.261: Unit

• Read Only Or Synthetic Opaque MVars: []
-/
#guard_msgs in
set_option egg.retryWithShapes false in
example (h : ∀ (f : Unit → Unit) (u : Unit), f u = .unit) : id Nat.add = id Nat.mul := by
  egg [h]

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
set_option egg.retryWithShapes true in
example (h : ∀ (f : Unit → Unit) (u : Unit), f u = .unit) : id Nat.add = id Nat.mul := by
  egg [h]
