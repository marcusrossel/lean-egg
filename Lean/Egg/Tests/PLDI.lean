import Egg
open Classical Lean.Omega.Decidable

-- This option enables tracking of various statistics for `egg` tactic calls. In VS Code, this
-- information can be viewed by hovering over the specific invocation of the `egg` tactic.
-- Alternatively, it can be viewed by in the *Infoview* when placing the cursor on the line of the
-- the specific invocation of the `egg` tactic.
--
-- The most important statistics are:
--
-- * total time: The total amount of time taken to complete the call to the `egg` tactic.
--
-- * eqsat time: The amount of time taken to run equality saturation in the backend.
--
-- * proof time: The length of the time span starting after equality saturation completed and ending
--               with the completion of the `egg` tactic. This time span mainly represents the
--               amount of time tak for proof reconstruction.
--
-- * iters:      The number of iterations run before equality saturation completed (potentially by
--               being aborted due to exceeding resource limits.)
--
-- * nodes:      The number of e-nodes contained in the e-graph when equality saturation completed
--               (potentially by being aborted due to exceeding resource limits.)
--
-- * classes:    The number of e-classes contained in the e-graph when equality saturation completed
--               (potentially by being aborted due to exceeding resource limits.)
--
-- * expl steps: The number of steps in the explanation produced by the respective equality
--               saturation backend. If the explanation length exceeds the limit set by the `egg`
--               tactic (1000 steps), then this value will only appear in an associated error
--               message.
set_option egg.reporting true

-- These options ensure that the explanations produced by the backends are visible in the
-- *Infoview*. The "Explanation" item shows the raw explanation string as returned by the backend.
-- The "Explanation Steps" item shows the explanation in a more readable form, as pretty-printed
-- Lean expressions.
set_option trace.egg.explanation false
set_option trace.egg.explanation.steps true








-- This section defines the required structures needed to state and prove the theorems below.

class SemilatticeSup (α : Type _) extends LE α, LT α where
  sup : α → α → α
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl
  le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b
  le_sup_left : ∀ a b : α, a ≤ sup a b
  le_sup_right : ∀ a b : α, b ≤ sup a b
  sup_le : ∀ a b c : α, a ≤ c → b ≤ c → sup a b ≤ c

infixl:68 " ⊔ " => SemilatticeSup.sup

variable [SemilatticeSup α] {a b : α}

def IsMin (a : α) : Prop :=
  ∀ ⦃b⦄, b ≤ a → a ≤ b

def SupIrred (a : α) : Prop :=
  ¬IsMin a ∧ ∀ ⦃b c⦄, b ⊔ c = a → b = a ∨ c = a

def SupPrime (a : α) : Prop :=
  ¬IsMin a ∧ ∀ ⦃b c⦄, a ≤ b ⊔ c → a ≤ b ∨ a ≤ c

-- These variables represent lemmas proven in Mathlib. We do not provide explicit proofs for them
-- as the proofs rely on further underlying theory, which we want to omit here.
variable
  (sup_eq_left  : ∀ [SemilatticeSup α] (a b : α), a ⊔ b = a ↔ b ≤ a)
  (sup_eq_right : ∀ [SemilatticeSup α] (a b : α), a ⊔ b = b ↔ a ≤ b)
  (left_lt_sup  : ∀ [SemilatticeSup α] (a b : α), a < a ⊔ b ↔ ¬b ≤ a)
  (right_lt_sup : ∀ [SemilatticeSup α] (a b : α), b < a ⊔ b ↔ ¬a ≤ b)








-- This section used *slotted* as the backend for the `egg` tactic.
namespace Slotted
set_option egg.slotted true

-- Notable:
-- * Total time < 1 second
-- * 19 explanation steps
theorem not_supPrime : ¬SupPrime a ↔ IsMin a ∨ ∃ b c, a ≤ b ⊔ c ∧ ¬a ≤ b ∧ ¬a ≤ c := by
  egg [not_forall, not_exists, not_or, not_not, not_and, not_imp, not_iff_iff_and_not_or_not_and,
       SupPrime]

-- Ensures that the listed lemmas (variables) are accessible in the following theorem.
include sup_eq_left sup_eq_right left_lt_sup right_lt_sup

-- Notable:
-- * Total time < 1 second
-- * 18 explanation steps
theorem not_supIrred : ¬SupIrred a ↔ IsMin a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  have h x y : x ⊔ y = a ∧ ¬x = a ∧ ¬y = a ↔ x ⊔ y = a ∧ x < a ∧ y < a := by
    simp +contextual [@eq_comm _ _ a, ne_eq, and_congr_right_iff,
                      sup_eq_left, sup_eq_right, left_lt_sup, right_lt_sup, implies_true]
  egg [not_forall, not_exists, not_or, not_not, not_and, not_imp, not_iff_iff_and_not_or_not_and,
       SupIrred, exists₂_congr h]

end Slotted








-- This section used *egg* as the backend for the `egg` tactic.
namespace Egg
set_option egg.slotted false

-- Notable:
-- * Over 4000 explanation steps
--
-- We use an "explanation length limit" in the `egg` tactic, to abort invocations which produce
-- explanations which are too long to process in a reasonable time. To (try to) process such
-- explanations anyway, increase the explanation length limit with
--
--    set_option egg.explLengthLimit <num>
--
-- Note that this may cause the tactic to take multiple minutes to complete.
theorem not_supPrime : ¬SupPrime a ↔ IsMin a ∨ ∃ b c, a ≤ b ⊔ c ∧ ¬a ≤ b ∧ ¬a ≤ c := by
  egg [not_forall, not_exists, not_or, not_not, not_and, not_imp, not_iff_iff_and_not_or_not_and,
       SupPrime]

-- Ensures that the listed lemmas (variables) are accessible in the following theorem.
include sup_eq_left sup_eq_right left_lt_sup right_lt_sup

-- Notable: We set the time limit to a practically infinite value here, to show that e-graph
--          explodes in this example. In comparison, this same theorem is proven with the *slotted*
--          backend in less than 1 second above. To inspect intermediate results, reduce the time
--          limit to a value like 10 (seconds) below. Note how quickly the number of e-nodes and
--          e-classes grows (by hovering over the tactic call and inspecting the info message).
set_option egg.timeLimit 1000000000000000000 in
theorem not_supIrred : ¬SupIrred a ↔ IsMin a ∨ ∃ b c, b ⊔ c = a ∧ b < a ∧ c < a := by
  have h x y : x ⊔ y = a ∧ ¬x = a ∧ ¬y = a ↔ x ⊔ y = a ∧ x < a ∧ y < a := by
    simp +contextual [@eq_comm _ _ a, ne_eq, and_congr_right_iff,
                      sup_eq_left, sup_eq_right, left_lt_sup, right_lt_sup, implies_true]
  egg [not_forall, not_exists, not_or, not_not, not_and, not_imp, not_iff_iff_and_not_or_not_and,
       SupIrred, exists₂_congr h]

end Egg
