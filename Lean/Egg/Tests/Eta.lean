import Egg

-- Note: We disable β-reduction as it can also solve many of these cases without η-reduction.
set_option egg.genEtaRw true
set_option egg.genBetaRw false

set_option egg.genEtaRw false in
/-- error: egg failed to prove the goal (reached time limit) -/
#guard_msgs in
example : (fun x => Nat.succ x) = Nat.succ := by
  egg

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

example : (eta 50 Nat.succ Nat) = Nat.succ := by
  egg

set_option egg.genEtaRw false in
/-- error: egg failed to prove the goal (reached time limit) -/
#guard_msgs in
example (a : Nat) (h : ∀ b : Nat, b.succ.add a = 0) : (10 |> fun x => Nat.succ x).add a = 0 := by
  egg [h]

example (a : Nat) (h : ∀ b : Nat, b.succ.add a = 0) : (10 |> fun x => Nat.succ x).add a = 0 := by
  egg [h]

-- Note: This used to break when we were using direct e-class substitution instead of small-step
--       substitution.
example : (fun x => x) = Add.add 0 := by
  egg [Nat.zero_add]

-- This tests that we correctly handle explanations which explicitly contain the small-step
-- substitition constructor.
example (f : α → α → α → α) : (fun a b => (fun x => (f a b) x)) = (fun a b => f a b) := by
  egg
