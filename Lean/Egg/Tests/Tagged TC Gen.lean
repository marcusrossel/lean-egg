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
info: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (0)
  [egg.rewrites] Tagged (1)
    [egg.rewrites] □r(⇔)
      [egg.rewrites] z = z
      [egg.rewrites] LHS MVars
          [?α: [inErasedTcInst, unconditionallyVisible],
           ?c: [isTcInst, unconditionallyVisible],
           ?u.80: [inErasedTcInst, unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?α: [inErasedTcInst, unconditionallyVisible],
           ?c: [isTcInst, unconditionallyVisible],
           ?u.80: [inErasedTcInst, unconditionallyVisible]]
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (0)
  [egg.rewrites] Structure Projections (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (0)
-/
#guard_msgs in
set_option trace.egg.rewrites true in
egg_no_defeq in
set_option egg.builtins false in
example : Nat.zero = Nat.zero := by
  egg basket


-- TODO(sorry): This actually shows in interesting difference to how we used to generate tc spec rws
--              (where we didn't require the new rw to have different directions from the old one):
/-
info: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (0)
  [egg.rewrites] Tagged (1)
    [egg.rewrites] □r(⇔)
      [egg.rewrites] z = z
      [egg.rewrites] LHS MVars
          [?α: [inErasedTcInst, unconditionallyVisible],
           ?c: [isTcInst, unconditionallyVisible],
           ?u.80: [inErasedTcInst, unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?α: [inErasedTcInst, unconditionallyVisible],
           ?c: [isTcInst, unconditionallyVisible],
           ?u.80: [inErasedTcInst, unconditionallyVisible]]
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (3)
    [egg.rewrites] □r<⊢0>(⇔)
      [egg.rewrites] z = z
      [egg.rewrites] LHS MVars
          []
      [egg.rewrites] RHS MVars
          []
    [egg.rewrites] □r<⊢0>[◂16,0](⇔)
      [egg.rewrites] z = 0
      [egg.rewrites] LHS MVars
          []
      [egg.rewrites] RHS MVars
          []
    [egg.rewrites] □r<⊢0>[◂16,1](⇔)
      [egg.rewrites] 0 = 0
      [egg.rewrites] LHS MVars
          []
      [egg.rewrites] RHS MVars
          []
  [egg.rewrites] Structure Projections (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (0)
-/
