import Egg

-- We have to turn of β-reduction in rewrites, as otherwise `thm` is reduced.
set_option egg.betaReduceRws false

theorem thm : ∀ y x : Nat, (fun _ => (fun _ => x) x) y = x :=
  fun _ _ => rfl

-- INVESTIGATE: It's expected that this proof fails (as the theorem is false). However, the e-graph
--              in this example grows infinitely while generating larger and larger bvar indices.
--              How/why does that happen?
example : (fun x => (fun a => (fun a => a) a) 0) = (fun x => x) := by
  sorry -- egg [thm]
