import Egg

set_option egg.genBetaRw true

example : (fun x => x) 0 = 0 := by
  sorry -- egg

example : (fun _ => 1) 0 = 1 := by
  sorry -- egg

example : (fun x => (fun y => y) x) 0 = 0 := by
  sorry -- egg

example : (fun x => (fun y => x) x) 0 = 0 := by
  sorry -- egg

example : (fun x => (fun y => x) 0) 1 = 1 := by
  sorry -- egg

example : id ((fun x => x + 1) 2) = id (1 + 2) := by
  sorry -- egg
