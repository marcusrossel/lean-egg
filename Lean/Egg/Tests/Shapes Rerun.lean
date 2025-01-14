import Egg

-- Checks that we rerun with shapes when proof reconstruction fails if `egg.retryWithShapes = true`.
-- Without rerunning with shapes, the first fails during proof reconstruction with the explanation
-- shown when setting `exitPoint := some .beforeProof`.

/--
error: egg failed to build proof step 2: unification failure for LHS of rewrite #0:

  HAdd.hAdd
vs
  ?m.257
in
  HAdd.hAdd
and
  ()

• Types: ⏎
  ?m.257: Unit

• Read Only Or Synthetic Opaque MVars: []
-/
#guard_msgs in
set_option egg.retryWithShapes false in
example (h : ∀ u : Unit, u = .unit) : Nat.add = Nat.mul := by
  egg [h]

/-- error: egg failed to prove the goal (reached time limit) -/
#guard_msgs in
set_option egg.retryWithShapes true in
example (h : ∀ u : Unit, u = .unit) : Nat.add = Nat.mul := by
  egg [h]
