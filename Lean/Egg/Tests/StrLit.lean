import Egg

-- TODO: We probably need to escape strings before we encode them.

-- TODO: The explanation produced by egg removes the quotes around the string.
set_option trace.egg true in
example (h : "Le" ++ "an" = "Lean") : "Le" ++ "an" = "Lean" := by
  sorry -- egg [h]
