import Egg

-- Tests containing examples of backend soundness issues.

-- TODO: This started breaking when we added more in depth reporting on why egg failed. I don't
--       understand how that's related at all, except that we now also parse the explanation even
--       when we don't do proof reconstruction, so this test case might have had this exact error
--       all along.

-- In this example egg finds a proof, but we're not performing proof reconstruction (which would be
-- impossible) as a result of setting `exitPoint := some .beforeProof`.
set_option trace.egg true
example : False := by
  have h : ∀ x : Unit, x = .unit := fun _ => rfl
  have : 1 + 2 = 0 := by sorry -- egg (config := { exitPoint := some .beforeProof }) [h]
  contradiction
