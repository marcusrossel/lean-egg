import Egg

set_option egg.subgoals true

example : 0 = 0 := by
  egg

example (h : a = b) : a = b := by
  egg [h]

-- Note: The condition is automatically proven, because during proof reconstruction we derive
--       unassigned propositional mvars by querying the e-graph.
example (h : True → a = b) : a = b := by
  egg [h]

/--
error: unsolved goals
α✝ : Sort u_1
a b : α✝
h : False → a = b
⊢ False
-/
#guard_msgs in
example (h : False → a = b) : a = b := by
  egg [h]

example (h₁ : x = y → a = b) (h₂ : x = y) : a = b := by
  egg [h₁, h₂]

example (h₁ : x = y → a = b) (h₂ : x = y) : a = b := by
  egg [h₁]
  exact h₂

-- Note: When condition subgoals are disabled, the given rewrite is applicable in both directions,
--       because the condition resolves `n` for the backward direction. But when condition subgoals
--       are enabled, the backward direction becomes non-applicable.
example (a b : Nat) (h : b ∣ a) : (a / b) * b = a := by
  egg [Nat.div_mul_cancel]
  assumption
