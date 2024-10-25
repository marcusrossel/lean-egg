import Egg

example : (fun x => (fun t _y => t) (fun z => x z)) = (fun (x : α → α) (_y : α) => x) := by
  egg
