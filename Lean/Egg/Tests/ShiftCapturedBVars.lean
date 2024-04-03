import Egg

-- We have to disable β-reduction as part of normalization, as otherwise `thm` is useless.
set_option egg.betaReduceRws false

theorem thm : ∀ x : Nat, x = (fun _ => x) (nat_lit 0) :=
  fun _ => rfl

-- In this example egg finds a proof, but we're not performing proof reconstruction (which would be
-- impossible) as a result of setting `exitPoint := some .beforeProof`.
set_option egg.shiftCapturedBVars false in
example : False := by
  have h : (fun x => x) = (fun y : Nat => (fun x => x) 1) := by
    egg (config := { exitPoint := some .beforeProof }) [thm]
  have : (fun x => x) 0 = (fun y => 1) 0 := by rw [h]
  contradiction

-- BUG: This generates a completely broken e-graph.
--      For example, a number node becomes equivalent to an application node.
set_option egg.shiftCapturedBVars true in
example : True := by
  have h : (fun x => x) = (fun y : Nat => (fun x => x) (nat_lit 1)) := by
    egg (config := { exitPoint := some .beforeProof, vizPath := "/Users/marcus/Desktop/dot" }) [thm]
  constructor
