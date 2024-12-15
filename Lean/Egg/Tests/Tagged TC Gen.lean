import Egg

-- This test checks that we generate type class lemmas for tagged rewrites.

class C (α) where
  z : α

instance : C Nat where
  z := 0

open C

@[egg]
theorem r [c : C α] : z (self := c) = z := rfl

/--
info: [egg.rewrites] Rewrites
  [egg.rewrites] Basic (0)
  [egg.rewrites] Tagged (1)
    [egg.rewrites] □0(⇔)
      [egg.rewrites] z = z
      [egg.rewrites] LHS MVars
          expr:  [?c, ?α]
          class: [?c]
          level: [?u.81]
      [egg.rewrites] RHS MVars
          expr:  [?c, ?α]
          class: [?c]
          level: [?u.81]
  [egg.rewrites] Builtin (0)
  [egg.rewrites] Derived (3)
    [egg.rewrites] □0<⊢>(⇔)
      [egg.rewrites] z = z
      [egg.rewrites] LHS MVars
          expr:  []
          class: []
          level: []
      [egg.rewrites] RHS MVars
          expr:  []
          class: []
          level: []
    [egg.rewrites] □0<⊢>[◂16,0](⇔)
      [egg.rewrites] z = 0
      [egg.rewrites] LHS MVars
          expr:  []
          class: []
          level: []
      [egg.rewrites] RHS MVars
          expr:  []
          class: []
          level: []
    [egg.rewrites] □0<⊢>[◂16,1](⇔)
      [egg.rewrites] 0 = 0
      [egg.rewrites] LHS MVars
          expr:  []
          class: []
          level: []
      [egg.rewrites] RHS MVars
          expr:  []
          class: []
          level: []
  [egg.rewrites] Definitional
  [egg.rewrites] Hypotheses (0)
  [egg.rewrites] Pruned (0)
-/
#guard_msgs in
set_option trace.egg.rewrites true in
set_option egg.builtins false in
set_option egg.builtins false in
set_option egg.beta false in
set_option egg.eta false in
set_option egg.natLit false in
set_option egg.levels false in
set_option egg.eraseProofs false in
set_option egg.eraseTCInstances false in
example : Nat.zero = Nat.zero := by
  egg!
