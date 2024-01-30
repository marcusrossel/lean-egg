import Egg

-- TODO: Can we run an iteration of the e-graph, then extract all terms and reduce them and then continue?

-- Tests for manually inspecting what terms look like with the `reduce` option.
set_option trace.egg true

example (a : Nat) (h : ∀ x : Nat, x + 1 = 1 + x) : a + 1 = 1 + a := by
  egg (config := { reduce := true }) [h]

-- This example shows that reduction can already reduce the proof goal to a degree that egg given
-- rewrite rules aren't required any more.
example (x : Nat) (h : ∀ x : Nat, x + 0 = x) : x = x + 0 := by
  egg (config := { reduce := true }) [h]

-- This example shows that reduction can already reduce the proof goal.
example (x : Nat) (h : ∀ x : Nat, x.add .zero = x) : x = x.add (Nat.zero.add .zero) := by
  egg [h]

-- TODO: Overview of problems regarding rewriting with/under binders and with/without type tags.
-- λ x : String, x
-- λ x : Nat, x
