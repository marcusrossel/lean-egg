import Egg

set_option egg.groundEqs false
set_option trace.egg.rewrites.explicit true
set_option linter.unusedVariables false

/--
trace: [egg.rewrites.explicit] Basic (1)
  [egg.rewrites.explicit] #0(⇒)❌[lhsSingleMVar]: h
    [egg.rewrites.explicit] ?x = ?x
    [egg.rewrites.explicit] LHS MVars
        [?x: [unconditionallyVisible]]
    [egg.rewrites.explicit] RHS MVars
        [?x: [unconditionallyVisible]]
-/
#guard_msgs in
example (h : ∀ x : Nat, x = x) : true = true := by
  egg [h]

/--
trace: [egg.rewrites.explicit] Basic (2)
  [egg.rewrites.explicit] #0(⇒): h
    [egg.rewrites.explicit] f ?x = ?x
    [egg.rewrites.explicit] LHS MVars
        [?x: [unconditionallyVisible], ?α: [unconditionallyVisible]]
    [egg.rewrites.explicit] RHS MVars
        [?x: [unconditionallyVisible]]
  [egg.rewrites.explicit] #0(⇐)❌[rhsMVarInclusion: [?α], lhsSingleMVar]: h
    [egg.rewrites.explicit] ?x = f ?x
    [egg.rewrites.explicit] LHS MVars
        [?x: [unconditionallyVisible]]
    [egg.rewrites.explicit] RHS MVars
        [?x: [unconditionallyVisible], ?α: [unconditionallyVisible]]
-/
#guard_msgs in
example (f : {α : Type} → α → α) (h : ∀ α (x : α), f x = x) : true = true := by
  egg [h]

/--
trace: [egg.rewrites.explicit] Basic (2)
  [egg.rewrites.explicit] #0(⇒): h
    [egg.rewrites.explicit] ?x + ?x = ?x
    [egg.rewrites.explicit] Conditions
      [egg.rewrites.explicit] Add ?α
    [egg.rewrites.explicit] LHS MVars
        [?α: [inErasedTcInst, inTcInstTerm, unconditionallyVisible],
         ?x: [unconditionallyVisible],
         ?inst✝: [inTcInstTerm, isTcInst]]
    [egg.rewrites.explicit] RHS MVars
        [?x: [unconditionallyVisible]]
  [egg.rewrites.explicit] #0(⇐)❌[tcMVarInclusion: [?α], rhsMVarInclusion: [?α], lhsSingleMVar]: h
    [egg.rewrites.explicit] ?x = ?x + ?x
    [egg.rewrites.explicit] Conditions
      [egg.rewrites.explicit] Add ?α
    [egg.rewrites.explicit] LHS MVars
        [?x: [unconditionallyVisible]]
    [egg.rewrites.explicit] RHS MVars
        [?α: [inErasedTcInst, inTcInstTerm, unconditionallyVisible],
         ?x: [unconditionallyVisible],
         ?inst✝: [inTcInstTerm, isTcInst]]
-/
#guard_msgs in
example (h : ∀ {α} [Add α] (x : α), x + x = x) : true = true := by
  egg [h]

/--
trace: [egg.rewrites.explicit] Basic (2)
  [egg.rewrites.explicit] #0(⇒): h
    [egg.rewrites.explicit] f ?n ⋯ = ?n
    [egg.rewrites.explicit] LHS MVars
        [?n: [inErasedProof, inProofTerm, unconditionallyVisible]]
    [egg.rewrites.explicit] RHS MVars
        [?n: [unconditionallyVisible]]
  [egg.rewrites.explicit] #0(⇐)❌[lhsSingleMVar]: h
    [egg.rewrites.explicit] ?n = f ?n ⋯
    [egg.rewrites.explicit] LHS MVars
        [?n: [unconditionallyVisible]]
    [egg.rewrites.explicit] RHS MVars
        [?n: [inErasedProof, inProofTerm, unconditionallyVisible]]
-/
#guard_msgs in
example (f : (n : Nat) → (0 < n + 1) → Nat) (h : ∀ n, f n (Nat.zero_lt_succ n) = n) : 0 = 0 := by
  egg [h]
