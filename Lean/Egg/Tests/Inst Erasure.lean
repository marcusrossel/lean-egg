import Egg

/--
info: [egg.encoded] Encoded
  [egg.encoded] Goal
    [egg.encoded] LHS: (app (app (app (app (app (app (const "HAdd.hAdd" 0 0 0) (const "Nat")) (const "Nat")) (const "Nat")) (inst (app (app (app (const "HAdd" 0 0 0) (const "Nat")) (const "Nat")) (const "Nat")))) (fvar 65)) (fvar 65))
    [egg.encoded] RHS: (app (app (app (app (app (app (const "HAdd.hAdd" 0 0 0) (const "Nat")) (const "Nat")) (const "Nat")) (inst (app (app (app (const "HAdd" 0 0 0) (const "Nat")) (const "Nat")) (const "Nat")))) (fvar 65)) (fvar 65))
  [egg.encoded] Guides
    [egg.encoded] (= (app (app (app (app (app (app (const "HAdd.hAdd" 0 0 0) (const "Nat")) (const "Nat")) (const "Nat")) (inst (app (app (app (const "HAdd" 0 0 0) (const "Nat")) (const "Nat")) (const "Nat")))) (fvar 65)) (fvar 65)) (app (app (app (app (app (app (const "HAdd.hAdd" 0 0 0) (const "Nat")) (const "Nat")) (const "Nat")) (inst (app (app (app (const "HAdd" 0 0 0) (const "Nat")) (const "Nat")) (const "Nat")))) (fvar 65)) (fvar 65)))
-/
#guard_msgs(info) in
set_option trace.egg.encoded true in
set_option egg.eraseTCInstances true in
set_option egg.builtins false in
set_option egg.genTcProjRws false in
example (a : Nat) : a + a = a + a := by
  egg (config := { exitPoint := some .beforeEqSat })
