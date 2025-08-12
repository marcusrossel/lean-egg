import Egg

-- This test ensures that condition mvars are correctly taken into account when determining the
-- valid direction of rewrites.

/--
trace: [egg.rewrites.explicit] Basic (1)
  [egg.rewrites.explicit] #0(⇐)
    [egg.rewrites.explicit] f ?a = f ?b
    [egg.rewrites.explicit] Conditions
      [egg.rewrites.explicit] ?a = ?b
    [egg.rewrites.explicit] LHS MVars
        [?a: [unconditionallyVisible]]
    [egg.rewrites.explicit] RHS MVars
        [?b: [unconditionallyVisible]]
-/
#guard_msgs in
set_option trace.egg.rewrites.explicit true in
set_option egg.groundEqs false in
example (f : Nat → Nat) (_h : ∀ a b : Nat, a = b → f b = f a) : true = true := by
  egg [_h]
