import Egg

-- The only difference between these two and the next two examples is the order of universe levels
-- in `[]`. That is, the second examples require commutativity of `Level.max`.

set_option egg.levels false in
example (f : α → γ) (g : β → δ) : List.map (Prod.map f g) [] = [] := by
  egg [List.map]

set_option egg.levels true in
example (f : α → γ) (g : β → δ) : List.map (Prod.map f g) [] = [] := by
  egg [List.map]

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
set_option egg.levels false in
example (f : α → γ) (g : β → δ) : List.map (Prod.map f g) [] = [] := by
  egg [List.map]

set_option egg.levels true in
example (f : α → γ) (g : β → δ) : List.map (Prod.map f g) [] = [] := by
  egg [List.map]

-- This example requires `Level.succ (Level.max _ _) = Level.max (Level.succ _) (Level.succ _)`.
example (h : ∀ γ : Type (max u v), γ = id γ) (α : Type u) (β : Type v) : (α × β) = id (α × β) := by
  egg [h]
