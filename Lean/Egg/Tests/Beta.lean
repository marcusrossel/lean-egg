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

-- TODO: It seems that both β-reduction steps are being performed in one go here. While this is cool
--       in practice it's probably not what we want, as this means that in `beta_reduce` we're
--       reducing classes which have only been added by β-reduction in the first place.
example : (fun x => (fun _ => x) 0) 1 = 1 := by
  egg

example : id ((fun x => x + 1) 2) = id (2 + 1) := by
  egg
