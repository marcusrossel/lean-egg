import Egg

-- Note: We disable β-reduction as it can also solve many of these cases without η-reduction.
set_option egg.genEtaRw true
set_option egg.genBetaRw false

example : (fun x => Nat.succ x) = Nat.succ := by
  fail_if_success egg (config := { genEtaRw := false })
  rfl

example : (fun x => Nat.succ x) = Nat.succ := by
  egg

example : id (fun x => Nat.succ x) = id Nat.succ := by
  egg

example : (fun x => Nat.succ x) x = Nat.succ x := by
  egg

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

example (a : Nat) (h : ∀ b : Nat, b.succ.add a = 0) : (10 |> fun x => Nat.succ x).add a = 0 := by
  fail_if_success egg (config := { genEtaRw := false }) [h]
  apply h

example (a : Nat) (h : ∀ b : Nat, b.succ.add a = 0) : (10 |> fun x => Nat.succ x).add a = 0 := by
  egg [h]

-- BUG: I think this is a result of not handling explanations property `replace_loose_bvars`.
--      The intended sequence of rewrites in something like:
--
--      (fun x : Nat => x)
--      (fun x : Nat => 0 + x)        by Nat.zero_add
--      (fun x : Nat => Nat.add 0 x)  by type class projections
--      (fun x : Nat => Add.add 0 x)  by type class projections
--      Add.add 0                     by η
example : (fun x => x) = Add.add 0 := by
  sorry -- egg [Nat.zero_add]
