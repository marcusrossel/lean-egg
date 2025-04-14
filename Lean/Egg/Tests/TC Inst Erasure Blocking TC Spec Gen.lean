import Egg
open scoped Egg

-- We used to have a bug where type class instance erasure blocked type class specialization,
-- because mvar collection was affected by the erasure and did not track instance mvars correctly.
-- This test checks that this isn't a problem anymore.

egg_no_defeq
set_option egg.builtins false
set_option egg.genTcProjRws false
set_option egg.genGroundEqs false
set_option trace.egg.rewrites true

/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇒): h
      [egg.rewrites] -?x = ?x
      [egg.rewrites] Conditions
        [egg.rewrites] Neg Int
      [egg.rewrites] LHS MVars
          [?x: [unconditionallyVisible], ?inst: [isTcInst, unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?x: [unconditionallyVisible]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (1)
    [egg.rewrites] #0<⊢0>(⇔)
      [egg.rewrites] -?m.57 = ?m.57
      [egg.rewrites] Conditions
        [egg.rewrites] Proven
          [egg.rewrites] Neg Int
      [egg.rewrites] LHS MVars
          [?m.57: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?m.57: [unconditionallyVisible]]
  [egg.rewrites] Structure Projections (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (1)
    [egg.rewrites] #0<←>(⇔)
      [egg.rewrites] -?m.64 = ?m.64
      [egg.rewrites] Conditions
        [egg.rewrites] Proven
          [egg.rewrites] Neg Int
      [egg.rewrites] LHS MVars
          [?m.64: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars [?m.64: [unconditionallyVisible]]
-/
#guard_msgs(info) in
example (h : ∀ [inst : Neg Int] (x : Int), @Neg.neg Int inst x = x) : (0 : Int) = (0 : Int) := by
  egg [h]

/-
info: [egg.rewrites] Rewrites
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇔): h
      [egg.rewrites] -?x = ?x
      [egg.rewrites] Conditions
        [egg.rewrites] Neg Int
      [egg.rewrites] LHS MVars
          [?inst: [.inTcInstTerm, .isTcInst], ?x: [.unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?x: [.unconditionallyVisible]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (1)
    [egg.rewrites] #0<←>(⇔)
      [egg.rewrites] -?m.125 = ?m.125
      [egg.rewrites] Conditions
        [egg.rewrites] Proven
          [egg.rewrites] Neg Int
      [egg.rewrites] LHS MVars
          [?m.125: [.unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?m.125: [.unconditionallyVisible]]
  [egg.rewrites] Definitional
    [egg.rewrites] Type Class Instances
  [egg.rewrites] Pruned (1)
    [egg.rewrites] #0<⊢>(⇔)
      [egg.rewrites] -?m.132 = ?m.132
      [egg.rewrites] Conditions
        [egg.rewrites] Proven
          [egg.rewrites] Neg Int
      [egg.rewrites] LHS MVars
          [?m.132: [.unconditionallyVisible]]
      [egg.rewrites] RHS MVars [?m.132: [.unconditionallyVisible]]
-/
-- #guard_msgs(info) in
example (h : ∀ [inst : Neg Int] (x : Int), @Neg.neg Int inst x = x) : (0 : Int) = (0 : Int) := by
  -- TODO: Why does type class specialization specialize as `<←>` instead of `<?>`, if the original
  --       rewrite is already bidirectional? Is it because it only looks at `.isTcInst`, instead of
  --       visibility?
  sorry -- egg [h]

-- BUG: Goal type specialization should generate a rewrite here.
example (h : ∀ (α) [inst : Neg α] (x : α), @Neg.neg α inst x = x) : (0 : Int) = (0 : Int) := by
  sorry -- egg [h]
