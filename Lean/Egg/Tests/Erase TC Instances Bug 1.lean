import Egg
import Lean

-- This used to fail with `egg: final proof contains expression mvar`, because we were replacing
-- proof steps of rfl-theorems with defeq steps during proof reconstruction. As a result, type class
-- instances appearing in rfl-theorems would not resolve erased type class instance mvars.

example : (fun _ => 1) 0 = 1 := by
  egg
