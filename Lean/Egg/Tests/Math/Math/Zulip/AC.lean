import Mathlib.Data.Real.Basic
import Egg

-- https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/.22Missing.20Tactics.22.20list/near/506705609

attribute [egg ac] add_assoc add_comm

example {x y z a : ℝ} (h : x + y + z = 0) : z + (a + x) + y = a := by
  egg +ac [h, zero_add]
