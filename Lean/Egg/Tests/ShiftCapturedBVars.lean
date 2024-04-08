import Egg

set_option egg.shiftCapturedBVars true in
example (h : ∀ x y : Nat, x = y ↔ y = x) : (∀ x y : Nat, x = y) ↔ (∀ a b : Nat, b = a + 0) := by
  egg [h, Nat.add_zero]

-- We have to disable β-reduction as part of normalization, as otherwise `thm₁,₂` are useless, and
-- disable β-reduction in egg, as this interferes with the test cases.
set_option egg.betaReduceRws false
set_option egg.genBetaRw false

-- This theorem is only applicable in the forward direction.
theorem thm₁ : ∀ x y : Nat, (x, y).fst = (fun _ => x) (nat_lit 1) :=
  fun _ _ => rfl

-- In this example egg finds a proof, but we're not performing proof reconstruction (which would be
-- impossible) as a result of setting `exitPoint := some .beforeProof`.
set_option egg.shiftCapturedBVars false in
example : False := by
  have h : (fun x => (x, 5).fst) = (fun _ : Nat => (fun x => x) 1) := by
    egg (config := { exitPoint := some .beforeProof }) [thm₁]
  have : (fun x => x) 0 = (fun y => 1) 0 := by rw [h]
  contradiction

set_option egg.shiftCapturedBVars true in
example : True := by
  fail_if_success -- This fails because egg could not find a proof.
    have : (fun x => (x, 5).fst) = (fun _ : Nat => (fun x => x) 1) := by egg [thm₁]
  constructor

theorem thm₂ : ∀ x : Nat, (fun _ => (fun _ => x) x) 0 = x :=
  fun _ => rfl

-- TODO: This seems to cause an infinite loop or at least extremely long runtime in
--       `shifted_subst_for_pat` or `subst`. I think what is happening is that `thm₂` is applied in
--       the backward direction over and over again which quickly blows up the e-graph.
--       Investigate further what's happening by somehow tracing `shifted_subst_for_pat`.
set_option egg.shiftCapturedBVars true in
example : True := by
  have : (fun x => (fun a => (fun a => a) a) 0) = (fun x => x) := by sorry -- egg [thm₂]
  constructor


-- Unrelated to capture avoidance:
--
-- TODO: If we have a theorem like `(fun a b => a) x y = x`, it's only applicable in the forward
--       direction. But once we β-reduce it, it's applicable in both directions. I think that can
--       cause problems during reconstruction as we cannot reconstruct the assignment of `y`.
