import Egg
open scoped Egg

-- TODO: This should generate a type class projection reduction from HAdd.hAdd to Add.add.
--       It doesn't because `α` and the `inst : Add α` are bvars.
--       To fix this, the tc-proj generator should generate fvars for the given bvars, perform the
--       reduction, and then over any remaining bvar-fvars.
-- #guard_msgs in
set_option trace.egg true in
set_option egg.builtins false in
example (h : (fun (α) [Mul α] (x y : α) => x * y) = a) : true = true := by
  sorry -- egg [h]

-- TODO: This should generate a goal type specialization for `h`, but I think it doesn't for the
--       same reason as outlined above.
example (h : ∀ {α} [Add α] (a : α), a + a = a) : 1 + 1 = 1 := by
  sorry -- egg [h]

-- This test ensures that projection reductions are produced for terms appearing in binder domains.
/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Basic (1)
    [egg.rewrites] #0(⇔): h
      [egg.rewrites] z = z
      [egg.rewrites] Conditions
        [egg.rewrites] x * y = z
      [egg.rewrites] LHS MVars
          []
      [egg.rewrites] RHS MVars
          []
  [egg.rewrites] Tagged (0)
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (2)
    [egg.rewrites] #0[0?69632,0](⇔)
      [egg.rewrites] HMul.hMul = Mul.mul
      [egg.rewrites] LHS MVars
          []
      [egg.rewrites] RHS MVars
          []
    [egg.rewrites] #0[0?69632,1](⇔)
      [egg.rewrites] Mul.mul = Nat.mul
      [egg.rewrites] LHS MVars
          []
      [egg.rewrites] RHS MVars
          []
  [egg.rewrites] Definitional
  [egg.rewrites] Hypotheses (0)
  [egg.rewrites] Pruned (0)
-/
#guard_msgs(info) in
set_option trace.egg.rewrites true in
egg_no_defeq in
set_option egg.builtins false in
example (x : Nat) (h : ∀ (_ : x * y = z), z = z) : x = x := by
  egg [h]
