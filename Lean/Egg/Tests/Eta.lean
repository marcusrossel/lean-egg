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

example : (fun x => (fun y => Nat.succ y) x) = Nat.succ := by
  egg (config := { genEtaRw := true })

example : (fun x => (fun y => Nat.succ y) x) x = Nat.succ x := by
  egg (config := { genEtaRw := true })

-- TODO: Is this an infinite loop in `eta_shift`?
example : id (fun x => (fun y => Nat.succ y) x) = id Nat.succ := by
  sorry -- egg (config := { genEtaRw := true })
