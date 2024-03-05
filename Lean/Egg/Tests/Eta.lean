import Egg

example : (fun x => Nat.succ x) = Nat.succ := by
  fail_if_success egg (config := { genEtaRw := false })
  rfl

example : (fun x => Nat.succ x) = Nat.succ := by
  egg (config := { genEtaRw := true })

example : id (fun x => Nat.succ x) = id Nat.succ := by
  egg (config := { genEtaRw := true })

example : (fun x => Nat.succ x) x = Nat.succ x := by
  egg (config := { genEtaRw := true })

elab "eta" n:num fn:ident ty:term : term => open Lean.Elab.Term in do
  let rec go (n : Nat) :=
    if n = 0
    then elabTerm fn none
    else return .lam `x (← elabTerm ty none) (.app (← go <| n - 1) (.bvar 0)) .default
  go n.getNat

example : (eta 2 Nat.succ Nat) = Nat.succ := by
  egg (config := { genEtaRw := true })

example : (eta 2 Nat.succ Nat) x = Nat.succ x := by
  egg (config := { genEtaRw := true })

example : id (eta 2 Nat.succ Nat) = id Nat.succ := by
  egg (config := { genEtaRw := true })

example : (eta 10 Nat.succ Nat) = Nat.succ := by
  egg (config := { genEtaRw := true })

example (a : Nat) (h : ∀ b : Nat, b.succ.add a = 0) : (10 |> fun x => Nat.succ x).add a = 0 := by
  fail_if_success egg (config := { genEtaRw := false }) [h]
  apply h

example (a : Nat) (h : ∀ b : Nat, b.succ.add a = 0) : (10 |> fun x => Nat.succ x).add a = 0 := by
  egg (config := { genEtaRw := true }) [h]
