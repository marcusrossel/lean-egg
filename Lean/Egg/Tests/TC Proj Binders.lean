import Egg

set_option linter.unusedVariables false

-- TODO: This should generate a type class projection reduction from HAdd.hAdd to Add.add.
--       It doesn't because `α` and the `inst : Add α` are bvars.
--       To fix this, the tc-proj generator should generate fvars for the given bvars, perform the
--       reduction, and then over any remaining bvar-fvars.
-- #guard_msgs in
set_option egg.builtins false in
example (h : (fun (α) [Mul α] (x y : α) => x * y) = a) : true = true := by
  sorry -- egg [h]

-- TODO: This should generate a goal type specialization for `h`, but I think it doesn't for the
--       same reason as outlined above.
example (h : ∀ {α} [Add α] (a : α), a + a = a) : 1 + 1 = 1 := by
  sorry -- egg [h]

-- This test ensures that projection reductions are produced for terms appearing in binder domains.
/--
trace: [egg.rewrites.tcProj] Type Class Projections (4)
  [egg.rewrites.tcProj] #0[0?69632,0](⇒)
    [egg.rewrites.tcProj] HMul.hMul = Mul.mul
    [egg.rewrites.tcProj] LHS MVars
        []
    [egg.rewrites.tcProj] RHS MVars
        []
  [egg.rewrites.tcProj] #0[0?69632,0](⇐)
    [egg.rewrites.tcProj] Mul.mul = HMul.hMul
    [egg.rewrites.tcProj] LHS MVars
        []
    [egg.rewrites.tcProj] RHS MVars
        []
  [egg.rewrites.tcProj] #0[0?69632,1](⇒)
    [egg.rewrites.tcProj] Mul.mul = Nat.mul
    [egg.rewrites.tcProj] LHS MVars
        []
    [egg.rewrites.tcProj] RHS MVars
        []
  [egg.rewrites.tcProj] #0[0?69632,1](⇐)
    [egg.rewrites.tcProj] Nat.mul = Mul.mul
    [egg.rewrites.tcProj] LHS MVars
        []
    [egg.rewrites.tcProj] RHS MVars
        []
-/
#guard_msgs in
set_option trace.egg.rewrites.tcProj true in
set_option egg.builtins false in
example (x : Nat) (h : ∀ (_ : x * y = z), z = z) : x = x := by
  egg [h]
