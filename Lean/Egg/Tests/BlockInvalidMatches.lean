import Egg

-- We have to disable β-reduction as part of normalization, as otherwise `thm` is useless.
set_option egg.betaReduceRws false

theorem thm₁ : ∀ y x : Nat, (fun _ => (fun _ => x) x) y = x :=
  fun _ _ => rfl

-- In this example egg finds a proof, but we're not performing proof reconstruction (which would be
-- impossible) as a result of setting `exitPoint := some .beforeProof`.
set_option egg.blockInvalidMatches false in
set_option egg.shiftCapturedBVars false in
example : False := by
  have h : (fun x => (fun a => (fun a => a) a) 0) = (fun x => x) := by
    egg (config := { exitPoint := some .beforeProof }) [thm₁]
  have : (fun _ => 0) 1 = (fun x => x) 1 := by rw [h]
  contradiction

-- This test covers Condition (2) of valid matches.
/- error: egg failed to prove goal -/
-- #guard_msgs in
set_option egg.blockInvalidMatches true in
example : (fun x => (fun a => (fun a => a) a) 0) = (fun x => x) := by
  sorry -- egg (config := { exitPoint := some .beforeProof }) [thm₁]
  -- TODO: This started failing (in the sense of seeming to loop infinitely) once we started adding
  --       all rewrites to the e-graph as facts. That is, when `thm₁` became part of the e-graph.
  --       The problem then seems to be β-reduction. Setting `egg.genBetaRw` to false doesn't loop.

-- This theorem is only applicable in the backward direction.
theorem thm₂ : ∀ x y : Nat, x = (fun _ => x) y :=
  fun _ _ => rfl

-- This test covers Condition (1) of valid matches.
set_option egg.blockInvalidMatches true in
/-- error: egg failed to prove goal -/
#guard_msgs in
example : (fun x => x) = (fun _ : Nat => (fun x => x) 1) := by
  egg [thm₂]
