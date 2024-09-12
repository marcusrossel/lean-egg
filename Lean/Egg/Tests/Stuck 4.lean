import Egg

-- This used to get stuck because of an integer underflow ocurring in the e-class analysis for loose
-- bound variables, as a result of down shifts. I think this happened because of a shift node with a
-- self-loop. My assumption is that e-class analysis values for nodes with self-loops are
-- constructed by performing all of the potentially recursive calls to nested e-class analysis
-- values until a fixed point is reached. For down-shift nodes with self-loops, this fixed point
-- would be reached when the bvar index hits 0. As a result of integer underflow, `make` would get
-- stuck in constructing an ever growing loose bound variable e-class analysis set working its way
-- down from 2^64. The fix was therefore to use saturating subtraction when applying downward
-- shifts. I'm not sure if this is actually a proper solution or just a bandaid. There might be a
-- more fundamental underlying problem with loops of shift nodes (e.g. shouldn't the same problem
-- occur when we have a self-loop on an up-shift node?).
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
