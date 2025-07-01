import Egg
open scoped Egg

-- This test checks that we generate type class lemmas for tagged rewrites.

class C (α) where
  z : α

instance : C Nat where
  z := 0

open C

@[egg basket]
theorem r [c : C α] : z (self := c) = z := rfl

/--
trace: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (0)
  [egg.rewrites] Tagged (1)
    [egg.rewrites] □r(⇒)
      [egg.rewrites] z = z
      [egg.rewrites] LHS MVars
          [?c: [isTcInst],
           ?α: [inErasedTcInst, unconditionallyVisible],
           ?u.137: [inErasedTcInst, unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?c: [isTcInst],
           ?α: [inErasedTcInst, unconditionallyVisible],
           ?u.137: [inErasedTcInst, unconditionallyVisible]]
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (0)
  [egg.rewrites] Structure Projections (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (1)
    [egg.rewrites] □r(⇐) by □r
      [egg.rewrites] z = z
      [egg.rewrites] LHS MVars
          [?c: [isTcInst],
           ?α: [inErasedTcInst, unconditionallyVisible],
           ?u.137: [inErasedTcInst, unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?c: [isTcInst],
           ?α: [inErasedTcInst, unconditionallyVisible],
           ?u.137: [inErasedTcInst, unconditionallyVisible]]
-/
#guard_msgs in
set_option trace.egg.rewrites true in
egg_no_defeq in
set_option egg.builtins false in
example : Nat.zero = Nat.zero := by
  egg +basket
