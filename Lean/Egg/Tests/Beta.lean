import Egg

set_option egg.genBetaRw true

example : (fun x => x) 0 = 0 := by
  egg

example : (fun _ => 1) 0 = 1 := by
  egg

-- BUG: While the explanation indicates that both β-reduction steps are being performed in one go,
--      the (graphviz exported) e-graphs actually show that both β-reductions happen one after
--      another. Thus, this demonstrates that we're not handling justifications correctly.
--      We would *want* the explanation to look as follows.
--
--      (app (λ (const Nat) (app (λ (const Nat) (bvar 0)) (bvar 0))) (lit 0))
--      (app (λ (const Nat) (Rewrite<= ≡β (bvar 0)) (lit 0))
--      (Rewrite<= ≡β (lit 0))
example : (fun x => (fun y => y) x) 0 = 0 := by
  egg

example : (fun x => (fun _ => x) x) 0 = 0 := by
  egg

example : (fun x => (fun _ => x) 0) 1 = 1 := by
  egg

example : id ((fun x => x + 1) 2) = id (2 + 1) := by
  egg
