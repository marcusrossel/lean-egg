import Egg

example : (fun x => (fun t _y => t) (fun z => x z)) = (fun (x : α → α) (_y : α) => x) := by
  egg

variable (m : Type → Type) (map : {α β : Type _} → (α → β) → m α → m β)

example (f : α → β → β) (g : β → β) (arg : m β) (ω : α) :
    map (f ω) (map g arg) = map (fun x => (f ω) (g x)) arg := by
  sorry -- Which rewrites should prove this?
