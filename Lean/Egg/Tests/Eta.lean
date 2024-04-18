import Egg

-- Note: We disable β-reduction as it can also solve many of these cases without η-reduction.
set_option egg.genEtaRw true
set_option egg.genBetaRw false

set_option egg.genEtaRw false in
example : (fun x => Nat.succ x) = Nat.succ := by
  fail_if_success egg
  rfl

example : (fun x => Nat.succ x) = Nat.succ := by
  egg

example : id (fun x => Nat.succ x) = id Nat.succ := by
  egg

example : (fun x => Nat.succ x) x = Nat.succ x := by
  egg

example (f : Nat → Nat) (h : f = g) : (fun x : Nat => f x) y = g y := by
  egg [h]

example (f : Nat → Nat) (h : f y = g) : (fun x : Nat => f x) y = g := by
  egg [h]

elab "eta" n:num fn:ident ty:term : term => open Lean.Elab.Term in do
  let rec go (n : Nat) :=
    if n = 0
    then elabTerm fn none
    else return .lam `x (← elabTerm ty none) (.app (← go <| n - 1) (.bvar 0)) .default
  go n.getNat

example : (eta 2 Nat.succ Nat) = Nat.succ := by
  egg

example : (eta 2 Nat.succ Nat) x = Nat.succ x := by
  egg

example : id (eta 2 Nat.succ Nat) = id Nat.succ := by
  egg

example : (eta 10 Nat.succ Nat) = Nat.succ := by
  egg

set_option egg.genEtaRw false in
example (a : Nat) (h : ∀ b : Nat, b.succ.add a = 0) : (10 |> fun x => Nat.succ x).add a = 0 := by
  fail_if_success egg [h]
  apply h

example (a : Nat) (h : ∀ b : Nat, b.succ.add a = 0) : (10 |> fun x => Nat.succ x).add a = 0 := by
  egg [h]

-- BUG: We're not handling justifications in `subst` correctly, yet. Thus, explanations break.
example : (fun x => x) = Add.add 0 := by
  sorry -- egg [Nat.zero_add]

/- TODO: Why is proof reconstruction failing here? The explanation seems totally fine:

  (app (app (λ (const Nat) (app f (bvar 0))) y) y)
  (app (app (Rewrite=> ≡η f) y) y)
  (app (Rewrite=> #0 g) y)
  (Rewrite<= #1-rev (app (app i y) (lit 0)))
  (app (app (Rewrite<= ≡η (λ (const Nat) (app i (bvar 0)))) y) (lit 0))

Even stranger, if you flip the LHS and RHS of the goal, it suddenly works. The produced explanation
in that case is the same just backwards. So a hacky fix would be to always obtain explanations from
egg in both directions and if one fails try the other.
-/
example (f i : Nat → Nat → Nat) (h₁ : f y = g) (h₂ : g y = i y (nat_lit 0)) :
    (f ·) y y = (i ·) y (nat_lit 0) := by
  sorry -- egg [h₁, h₂]
