import Egg

set_option egg.builtins false
set_option trace.egg.rewrites.tcProj true

/-- trace: [egg.rewrites.tcProj] Type Class Projections (0) -/
#guard_msgs in
example : true = true := by
  egg

/--
trace: [egg.rewrites.tcProj] Type Class Projections (2)
  [egg.rewrites.tcProj] ⊢[▸64,0](⇒)
    [egg.rewrites.tcProj] @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)) = nat_lit 0
    [egg.rewrites.tcProj] LHS MVars
        []
    [egg.rewrites.tcProj] RHS MVars
        []
  [egg.rewrites.tcProj] ⊢[▸64,0](⇐)
    [egg.rewrites.tcProj] nat_lit 0 = @OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))
    [egg.rewrites.tcProj] LHS MVars
        []
    [egg.rewrites.tcProj] RHS MVars
        []
-/
#guard_msgs in
set_option pp.explicit true in
example : 0 = 0 := by
  egg

-- This should not generate any reductions, as `List.append` doesn't appear anywhere.
/-- trace: [egg.rewrites.tcProj] Type Class Projections (0) -/
#guard_msgs in
example (l : List α) : l ++ l = l ++ l := by
  egg

-- TODO:
-- This should only generate reductions, between `HAppend` and `List.append`, as `Append` doesn't
-- appear anywhere.
/--
trace: [egg.rewrites.tcProj] Type Class Projections (4)
  [egg.rewrites.tcProj] ⊢[▸4096,0](⇒)
    [egg.rewrites.tcProj] HAppend.hAppend = Append.append
    [egg.rewrites.tcProj] LHS MVars
        []
    [egg.rewrites.tcProj] RHS MVars
        []
  [egg.rewrites.tcProj] ⊢[▸4096,0](⇐)
    [egg.rewrites.tcProj] Append.append = HAppend.hAppend
    [egg.rewrites.tcProj] LHS MVars
        []
    [egg.rewrites.tcProj] RHS MVars
        []
  [egg.rewrites.tcProj] ⊢[▸4096,1](⇒)
    [egg.rewrites.tcProj] Append.append = List.append
    [egg.rewrites.tcProj] LHS MVars
        []
    [egg.rewrites.tcProj] RHS MVars
        []
  [egg.rewrites.tcProj] ⊢[▸4096,1](⇐)
    [egg.rewrites.tcProj] List.append = Append.append
    [egg.rewrites.tcProj] LHS MVars
        []
    [egg.rewrites.tcProj] RHS MVars
        []
-/
#guard_msgs in
example (l : List α) : l ++ l = l ++ l := by
  egg [List.append]

-- This should only generate reductions, between `HAppend` and `Append`, as `List.append` doesn't
-- appear anywhere.
/--
trace: [egg.rewrites.tcProj] Type Class Projections (2)
  [egg.rewrites.tcProj] ⊢[◂4096,0](⇒)
    [egg.rewrites.tcProj] HAppend.hAppend = Append.append
    [egg.rewrites.tcProj] LHS MVars
        []
    [egg.rewrites.tcProj] RHS MVars
        []
  [egg.rewrites.tcProj] ⊢[◂4096,0](⇐)
    [egg.rewrites.tcProj] Append.append = HAppend.hAppend
    [egg.rewrites.tcProj] LHS MVars
        []
    [egg.rewrites.tcProj] RHS MVars
        []
-/
#guard_msgs in
example (l : List α) : l ++ l = Append.append l l := by
  egg






-- TODO: Nat-lit related symbols are a bit special, so the following tests need further consideration.

/--
trace: [egg.rewrites.tcProj] Type Class Projections (4)
  [egg.rewrites.tcProj] ⊢[▸4096,1](⇒)
    [egg.rewrites.tcProj] Add.add = Nat.add
    [egg.rewrites.tcProj] LHS MVars
        []
    [egg.rewrites.tcProj] RHS MVars
        []
  [egg.rewrites.tcProj] ⊢[▸4096,1](⇐)
    [egg.rewrites.tcProj] Nat.add = Add.add
    [egg.rewrites.tcProj] LHS MVars
        []
    [egg.rewrites.tcProj] RHS MVars
        []
  [egg.rewrites.tcProj] ⊢[▸4096,0](⇒)
    [egg.rewrites.tcProj] HAdd.hAdd = Add.add
    [egg.rewrites.tcProj] LHS MVars
        []
    [egg.rewrites.tcProj] RHS MVars
        []
  [egg.rewrites.tcProj] ⊢[▸4096,0](⇐)
    [egg.rewrites.tcProj] Add.add = HAdd.hAdd
    [egg.rewrites.tcProj] LHS MVars
        []
    [egg.rewrites.tcProj] RHS MVars
        []
-/
#guard_msgs in
example (a b : Nat) : a + b = a + b := by
  egg -- TODO: This should not generate any reductions, as `Nat.add` doesn't appear anywhere.
      --       Although, we do have nat-lit rewrites enabled, so it *does*. Figure out how to deal
      --       with this.

/--
trace: [egg.rewrites.tcProj] Type Class Projections (4)
  [egg.rewrites.tcProj] ⊢[◂4096,1](⇒)
    [egg.rewrites.tcProj] Add.add = Nat.add
    [egg.rewrites.tcProj] LHS MVars
        []
    [egg.rewrites.tcProj] RHS MVars
        []
  [egg.rewrites.tcProj] ⊢[◂4096,1](⇐)
    [egg.rewrites.tcProj] Nat.add = Add.add
    [egg.rewrites.tcProj] LHS MVars
        []
    [egg.rewrites.tcProj] RHS MVars
        []
  [egg.rewrites.tcProj] ⊢[◂4096,0](⇒)
    [egg.rewrites.tcProj] HAdd.hAdd = Add.add
    [egg.rewrites.tcProj] LHS MVars
        []
    [egg.rewrites.tcProj] RHS MVars
        []
  [egg.rewrites.tcProj] ⊢[◂4096,0](⇐)
    [egg.rewrites.tcProj] Add.add = HAdd.hAdd
    [egg.rewrites.tcProj] LHS MVars
        []
    [egg.rewrites.tcProj] RHS MVars
        []
-/
#guard_msgs in
example (a b : Nat) : a + b = Add.add a b := by
  egg -- TODO: This should only generate the reductions for `HAdd` <=> `Add`.
