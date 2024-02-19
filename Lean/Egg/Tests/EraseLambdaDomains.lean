import Egg

example : (fun x => x) = (fun x => 0 + 0 + x) := by
  egg (config := { eraseLambdaDomains := false }) [Nat.zero_add]

-- BUG: proof reconstruction
example : (fun x => x) = (fun x => 0 + 0 + x) := by
  egg (config := { eraseLambdaDomains := true }) [Nat.zero_add]

example : (fun x => x) = (fun x => 0 + x) := by
  egg (config := { eraseLambdaDomains := false }) [Nat.zero_add]

example : (fun x => x) = (fun x => 0 + x) := by
  egg (config := { eraseLambdaDomains := true }) [Nat.zero_add]
