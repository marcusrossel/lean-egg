import Egg
open scoped Egg

egg_no_defeq
set_option egg.builtins false
set_option egg.tcProjs false
set_option egg.groundEqs false
set_option trace.egg.rewrites true

/--
trace: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇒)❌[lhsSingleMVar]: h
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
  [egg.rewrites] Pruned (1)
    [egg.rewrites] #0(⇐)❌[lhsSingleMVar] by #0
      [egg.rewrites] ?x = ?x
      [egg.rewrites] LHS MVars
          [?x: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?x: [unconditionallyVisible]]
-/
#guard_msgs(trace) in
example (h : ∀ x : Nat, x = x) : true = true := by
  egg [h]

/--
trace: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (2)
    [egg.rewrites] #0(⇒): h
      [egg.rewrites] f ?x = ?x
      [egg.rewrites] LHS MVars
          [?x: [unconditionallyVisible], ?α: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?x: [unconditionallyVisible]]
    [egg.rewrites] #0(⇐)❌[rhsMVarInclusion: [?α], lhsSingleMVar]: h
      [egg.rewrites] ?x = f ?x
      [egg.rewrites] LHS MVars
          [?x: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?x: [unconditionallyVisible], ?α: [unconditionallyVisible]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (0)
  [egg.rewrites] Structure Projections (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (0)
-/
#guard_msgs(trace) in
example (f : {α : Type} → α → α) (h : ∀ α (x : α), f x = x) : true = true := by
  egg [h]

/--
trace: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (2)
    [egg.rewrites] #0(⇒): h
      [egg.rewrites] ?x + ?x = ?x
      [egg.rewrites] Conditions
        [egg.rewrites] Add α
      [egg.rewrites] LHS MVars
          [?inst✝: [inTcInstTerm, isTcInst], ?x: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?x: [unconditionallyVisible]]
    [egg.rewrites] #0(⇐)❌[lhsSingleMVar]: h
      [egg.rewrites] ?x = ?x + ?x
      [egg.rewrites] Conditions
        [egg.rewrites] Add α
      [egg.rewrites] LHS MVars
          [?x: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?inst✝: [inTcInstTerm, isTcInst], ?x: [unconditionallyVisible]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (0)
  [egg.rewrites] Structure Projections (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (0)
-/
#guard_msgs(trace) in
example (h : ∀ [Add α] (x : α), x + x = x) : true = true := by
  egg [h]

/--
trace: [egg.rewrites] Rewrites
  [egg.rewrites] Intros (0)
  [egg.rewrites] Basic (2)
    [egg.rewrites] #0(⇒): h
      [egg.rewrites] f ?n ⋯ = ?n
      [egg.rewrites] LHS MVars
          [?n: [inErasedProof, inProofTerm, unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?n: [unconditionallyVisible]]
    [egg.rewrites] #0(⇐)❌[lhsSingleMVar]: h
      [egg.rewrites] ?n = f ?n ⋯
      [egg.rewrites] LHS MVars
          [?n: [unconditionallyVisible]]
      [egg.rewrites] RHS MVars
          [?n: [inErasedProof, inProofTerm, unconditionallyVisible]]
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (0)
  [egg.rewrites] Structure Projections (0)
  [egg.rewrites] Definitional
  [egg.rewrites] Pruned (0)
-/
#guard_msgs(trace) in
example (f : (n : Nat) → (0 < n + 1) → Nat) (h : ∀ n, f n (Nat.zero_lt_succ n) = n) : 0 = 0 := by
  egg [h]
