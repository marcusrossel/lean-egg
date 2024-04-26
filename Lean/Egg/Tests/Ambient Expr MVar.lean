import Egg
import Lean

variable (h : ∀ x : Prop, True = x)

example : True = True := by
  apply Eq.trans
  · egg [h]
  · rfl -- This assigns the mvar resulting from `Eq.trans`.

/--
error: unsolved goals
case b
h : ∀ (x : Prop), True = x
⊢ Prop
-/
#guard_msgs in
example : True = True := by
  apply Eq.trans
  · egg [h]
  · egg [h]
