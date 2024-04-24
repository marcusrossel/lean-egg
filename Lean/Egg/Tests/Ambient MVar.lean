import Egg
import Lean

example (h : ∀ x : Prop, True = x) : True = True := by
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
example (h : ∀ x : Prop, True = x) : True = True := by
  apply Eq.trans
  · egg [h]
  · egg [h]
