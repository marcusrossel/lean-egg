import Egg

set_option egg.genBetaRw true

example : (fun x => x) 0 = 0 := by
  egg

example : (fun _ => 1) 0 = 1 := by
  egg

example : (fun x => (fun y => y) x) 0 = 0 := by
  egg

example : (fun x => (fun _ => x) x) 0 = 0 := by
  egg

example : (fun x => (fun _ => x) 0) 1 = 1 := by
  egg

example : id ((fun x => x + 1) 2) = id (2 + 1) := by
  egg

example (h : y + 1 = z) : (fun x => y + 1) 0 = z := by
  egg [h]

-- Note: This used to break when using explicit e-class substitution.
example (h : y + 1 = z) : (fun x => x + 1) y = z := by
  egg [h]
