import Egg
open scoped Egg

egg_no_defeq
set_option egg.builtins false
set_option egg.genTcProjRws false
set_option egg.genGroundEqs false
set_option trace.egg.rewrites true

/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇔): h
      [egg.rewrites] ?x = ?x
      [egg.rewrites] LHS MVars
          [?x: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?x: [unconditionallyVisible]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (0)
  [egg.rewrites] Structure Projections (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (0)
-/
#guard_msgs(info) in
example (h : ∀ x : Nat, x = x) : true = true := by
  egg [h]

/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇒): h
      [egg.rewrites] f ?x = ?x
      [egg.rewrites] LHS MVars
          [?α: [unconditionallyVisible], ?x: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?x: [unconditionallyVisible]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (0)
  [egg.rewrites] Structure Projections (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (0)
-/
#guard_msgs(info) in
example (f : {α : Type} → α → α) (h : ∀ α (x : α), f x = x) : true = true := by
  egg [h]

-- TODO: Without type class instance erasure, the following rewrite #0 was only applicable in the
--       forward direction, but had not condition. Now it's applicable in both directions, but has
--       a condition. Thus, it seems we should be more conservative about adding type class
--       instances as conditions. Best case scenario here would be: we first only generate the
--       rewrite in the single applicable direction as before, without the condition. Then, we have
--       a rewrite generator, similar to type class specialization, which tries to increase the
--       applicable rewrite directions by adding type class instances as conditions.

/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇔): h
      [egg.rewrites] ?x + ?x = ?x
      [egg.rewrites] Conditions
        [egg.rewrites] Add α
      [egg.rewrites] LHS MVars
          [?x: [unconditionallyVisible], ?inst✝: [inTcInstTerm, isTcInst]]
      [egg.rewrites] RHS MVars
          [?x: [unconditionallyVisible]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (0)
  [egg.rewrites] Structure Projections (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (0)
-/
#guard_msgs(info) in
example (h : ∀ [Add α] (x : α), x + x = x) : true = true := by
  egg [h]

/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇔): h
      [egg.rewrites] f ?n ⋯ = ?n
      [egg.rewrites] LHS MVars
          [?n: [inErasedProof, inProofTerm, unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?n: [unconditionallyVisible]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (0)
  [egg.rewrites] Structure Projections (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (0)
-/
#guard_msgs(info) in
example (f : (n : Nat) → (0 < n + 1) → Nat) (h : ∀ n, f n (Nat.zero_lt_succ n) = n) : 0 = 0 := by
  egg [h]
