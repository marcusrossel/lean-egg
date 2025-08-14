import Egg

/--
trace: [egg.encoded] Encoded
  [egg.encoded] Goal
    [egg.encoded] LHS: (app (app (app (app (app (app (const "HAdd.hAdd" 0 0 0) (const "Nat")) (const "Nat")) (const "Nat")) (inst (app (app (app (const "HAdd" 0 0 0) (const "Nat")) (const "Nat")) (const "Nat")))) (fvar 71)) (fvar 71))
    [egg.encoded] RHS: (app (app (app (app (app (app (const "HAdd.hAdd" 0 0 0) (const "Nat")) (const "Nat")) (const "Nat")) (inst (app (app (app (const "HAdd" 0 0 0) (const "Nat")) (const "Nat")) (const "Nat")))) (fvar 71)) (fvar 71))
  [egg.encoded] Guides
    [egg.encoded] (= (app (app (app (app (app (app (const "HAdd.hAdd" 0 0 0) (const "Nat")) (const "Nat")) (const "Nat")) (inst (app (app (app (const "HAdd" 0 0 0) (const "Nat")) (const "Nat")) (const "Nat")))) (fvar 71)) (fvar 71)) (app (app (app (app (app (app (const "HAdd.hAdd" 0 0 0) (const "Nat")) (const "Nat")) (const "Nat")) (inst (app (app (app (const "HAdd" 0 0 0) (const "Nat")) (const "Nat")) (const "Nat")))) (fvar 71)) (fvar 71)))
-/
#guard_msgs in
set_option trace.egg.encoded true in
set_option egg.builtins false in
set_option egg.tcProjs false in
example (a : Nat) : a + a = a + a := by
  egg
