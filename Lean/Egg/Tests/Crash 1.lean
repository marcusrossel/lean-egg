import Egg

-- This used to crash. I don't recall why, but something related to unassigned variables during
-- substitution after e-matching. This seems to have been fixed by a change in how conditions are
-- handled.

axiom beq_ext {α : Type _} (inst1 : BEq α) (inst2 : BEq α)
  (h : ∀ x y, @BEq.beq _ inst1 x y = @BEq.beq _ inst2 x y) : inst1 = inst2

open Classical in
axiom beq_eq_decide {α : Type _} [BEq α] [LawfulBEq α] {a b : α} : (a == b) = decide (a = b)

/-- error: egg failed to prove the goal (saturated) -/
#guard_msgs in
theorem lawful_beq_subsingleton
    {α : Type _} (inst1 : BEq α) (inst2 : BEq α) [@LawfulBEq α inst1] [@LawfulBEq α inst2] :
    inst1 = inst2 := by
  apply beq_ext; intro x y
  egg [beq_eq_decide]
