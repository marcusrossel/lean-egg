import Egg

-- We have to disable β-reduction as part of normalization, as otherwise `thm` is useless.
set_option egg.betaReduceRws false

theorem thm : ∀ y x : Nat, (fun _ => (fun _ => x) x) y = x :=
  fun _ _ => rfl

-- In this example egg finds a proof, but we're not performing proof reconstruction (which would be
-- impossible) as a result of setting `exitPoint := some .beforeProof`.
set_option egg.blockInvalidMatches false in
example : False := by
  have h : (fun x => (fun a => (fun a => a) a) 0) = (fun x => x) := by
    egg (config := { exitPoint := some .beforeProof }) [thm]
  have : (fun _ => 0) 1 = (fun x => x) 1 := by rw [h]
  contradiction

set_option egg.blockInvalidMatches true in
example : True := by
  fail_if_success -- This fails because egg could not find a proof.
    have _ : (fun x => (fun a => (fun a => a) a) 0) = (fun x => x) := by
      egg (config := { exitPoint := some .beforeProof }) [thm]
  constructor

-- BUG: The rewrite can applied backwards in an invalid way as `shiftCapturedBVars` isn't enabled.
example : True := by
  have _ : (fun x => (fun a => (fun a => a) a) <| nat_lit 0) = (fun x => x) := by
    egg (config := { exitPoint := some .beforeProof }) [thm (nat_lit 0)]
  constructor
