import Egg

-- TODO: It seems that for strings not containing "(", ")", or " ", egg removes the surrounding
--       double-quotes in explanations. I think the problem comes somewhere from here:
--       https://docs.rs/symbolic_expressions/5.0.3/src/symbolic_expressions/formatter.rs.html#10-25

example : "a" = "a" := by
  sorry -- egg

example : "a\nb" = "a\nb" := by
  sorry -- egg

example : "" = "" := by
  egg

example : " " = " " := by
  egg

example : "a b" = "a b" := by
  egg

example : "(" = "(" := by
  egg

example : ")" = ")" := by
  egg

example (h : "Le " ++ " an" = "Le  an") : "Le " ++ " an" = "Le  an" := by
  egg [h]
