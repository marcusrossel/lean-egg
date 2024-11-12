import Egg

-- We have to disable bvar shifting, as this option implies that invalid match checking. That is,
-- turning off `egg.blockInvalidMatches` has no effect then.
set_option egg.shiftCapturedBVars false

-- We have to disable β-reduction as part of normalization, as otherwise `thm₁` and `thm₂` are
-- useless for our testing purposes. Also, we don't want β- or η-reduction affecting these test in
-- any way, so we disable them.
set_option egg.betaReduceRws false
set_option egg.etaReduceRws false
set_option egg.beta false
set_option egg.eta false

-- These tests cover Condition (1) of (in-)valid matches.
section «Condition 1»

-- This theorem is only applicable in the backward direction.
theorem thm₁ : ∀ x y : Nat, x = (fun _ => x) y :=
  fun _ _ => rfl

-- In this example egg finds a proof, but we're not performing proof reconstruction (which would be
-- impossible) as a result of setting `exitPoint := some .beforeProof`.
set_option egg.blockInvalidMatches false in
example : (fun x => x) = (fun _ : Nat => (fun x => x) 1) := by
  egg (config := { exitPoint := some .beforeProof }) [thm₁]

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
set_option egg.blockInvalidMatches true in
example : (fun x => x) = (fun _ : Nat => (fun x => x) 1) := by
  egg [thm₁]

end «Condition 1»

-- These tests cover Condition (2) of (in-)valid matches.
section «Condition 2»

theorem thm₂ : ∀ y x : Nat, (fun _ => (fun _ => x) x) y = x :=
  fun _ _ => rfl

-- In this example egg finds a proof, but we're not performing proof reconstruction (which would be
-- impossible) as a result of setting `exitPoint := some .beforeProof`.
set_option egg.blockInvalidMatches false in
example : False := by
  have h : (fun x => (fun a => (fun a => a) a) 0) = (fun x => x) := by
    egg (config := { exitPoint := some .beforeProof }) [thm₂]
  have : (fun _ => 0) 1 = (fun x => x) 1 := by rw [h]
  contradiction

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
set_option egg.blockInvalidMatches true in
example : (fun x => (fun a => (fun a => a) a) 0) = (fun x => x) := by
  egg [thm₂]

end «Condition 2»
