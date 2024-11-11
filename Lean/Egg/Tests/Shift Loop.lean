import Egg

-- This used to get stuck because of an integer underflow ocurring in the e-class analysis for loose
-- bound variables, as a result of down shifts. I think this happened because of a shift node with a
-- self-loop. I think there are multiple problems with looping shift-nodes. First, they can generate
-- infinitely many new nodes. E.g. if we have a +2 shift node with a self-loop and another e-node in
-- the same e-class which contains bvar 5, then we get copies of that e-node with bvar 7, 9, 11, ...
-- The second problem is analogous and occurs when constructing the loose bvar e-class analysis. My
-- assumption is that e-class analysis values for nodes with self-loops are constructed by
-- performing all of the potentially recursive calls to nested e-class analysis values until a fixed
-- point is reached. For shift nodes with self-loops there is no fixed point.
-- We address the latter problem by adding an arbitrary limit of 100 for cutting off loose bvar
-- e-class analyses.
--
-- I used to following workaround for the lack of reliable printing to stdout from Rust:
--
--   use std::fs::OpenOptions;
--   use std::io::prelude::*;
--   let mut file = OpenOptions::new().write(true).append(true).open("<path>").unwrap();
--   let _ = writeln!(file, "apply {}", rule);

variable {r : α → α → Prop} (s : α → Prop)

/-- error: egg failed to prove the goal (reached time limit) -/
#guard_msgs in
open Classical in
example : ¬(∃ a, ∀ b, s b → r b a) ↔ (∀ a, ∃ b, s b → ¬r b a) := by
  egg [not_exists, exists_prop, not_and]
