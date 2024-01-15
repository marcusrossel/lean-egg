import Egg

-- Tests involving polymorphic types.

example : ([] : List α) = [] := by
  egg

example {l₁ l₂ : List α} : l₁ ++ l₂ = (l₂.reverse ++ l₁.reverse).reverse := by
  egg [List.reverse_append, List.reverse_reverse]
