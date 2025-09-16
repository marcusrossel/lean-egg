import Egg

/-- warning: conditions are only blocked when `egg.subgoals` is `true` -/
#guard_msgs in
example : True := by
  egg blocking True

/-- error: blocking terms must be propositions -/
#guard_msgs in
example : True := by
  egg blocking 0

set_option egg.subgoals true

example : True := by
  egg blocking True

variable {P : Prop}

/--
error: unsolved goals
P : Prop
h : P → False
⊢ P
-/
#guard_msgs in
example (h : P → False) : False := by
  egg [h]

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
example (h : P → False) : False := by
  egg [h] blocking P

/--
error: unsolved goals
P Q : Prop
hq : Q
h₁ : P → False
h₂ : Q → False
⊢ P
-/
#guard_msgs in
example {Q : Prop} (hq : Q) (h₁ : P → False) (h₂ : Q → False) : False := by
  egg [h₁, h₂]

example {Q : Prop} (hq : Q) (_h₁ : P → False) (h₂ : Q → False) : False := by
  egg [_h₁, h₂] blocking P
  exact hq

example (h : ∀ n, n > 0 → P) : P := by
  egg [h]
  · exact 1
  · simp

example (h : ∀ n, n > 1 → n > 0) : 2 > 0 := by
  egg [h]
  simp

example {f : Nat → Nat} (h : ∀ n, n > 2 → f n = x) : f 3 = x := by
  egg [h]
  simp
