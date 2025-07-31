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
example (a b : Nat) : a + b = Nat.add a b := by
  egg -- TODO: This should fuze the reductions into `HAdd` <=> `Nat.add`.

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
