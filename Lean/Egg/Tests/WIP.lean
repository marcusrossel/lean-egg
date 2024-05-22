import Egg

-- BUG: Hangs if you set true to false:
set_option egg.genTcSpecRws true in
example (a b : α) [Add α] (h : ∀ x y : α, x + y = y + x) : a + b = b + a := by
  egg [h]

theorem beq_ext {α : Type _} (inst1 : BEq α) (inst2 : BEq α) (h : ∀ x y, @BEq.beq _ inst1 x y = @BEq.beq _ inst2 x y) : inst1 = inst2 := sorry
open Classical in
theorem beq_eq_decide {α : Type _} [BEq α] [LawfulBEq α] {a b : α} : (a == b) = decide (a = b) := sorry

-- CRASH: The rewrite `beq_eq_decide` is considered to be conditional with condition `LawfulBEq α`,
--        which then remains unassigned when substituting after e-matching.
theorem lawful_beq_subsingleton {α : Type _} (inst1 : BEq α) (inst2 : BEq α)
    [@LawfulBEq α inst1] [@LawfulBEq α inst2] :
    inst1 = inst2 := by
  apply beq_ext
  intro x y
  egg (config := { exitPoint := some .beforeEqSat }) [beq_eq_decide]

-- CRASH: When turning on proof erasure.
set_option egg.eraseProofs false in
theorem Array.get_set_ne (a : Array α) (i : Fin a.size) {j : Nat} (v : α) (hj : j < a.size)
    (h : i.1 ≠ j) : (a.set i v)[j]'(by simp [*]) = a[j] := by
  sorry -- egg [set, Array.getElem_eq_data_get, List.get_set_ne _ h]

-- The universe mvars (or universe params if you make this a theorem instead of an example) are
-- different for the respective `α`s, so this doesn't hold by reflexivity. But `simp` can somehow
-- prove this.
example : (∀ α (l : List α), l.length = l.length) ↔ (∀ α (l : List α), l.length = l.length) := by
  set_option trace.egg true in egg

-- For rewrites involving dependent arguments, we can easily get an incorrect motive. E.g. when
-- rewriting the condition in ite without chaning the type class instance:
set_option trace.egg true in
example : (if 0 = 0 then 0 else 1) = 0 := by
  have h1 : (0 = 0) = True := eq_self 0
  have h2 : 0 = 0 := rfl
  egg [h1, h2, ite_congr, if_true]

-- For typeclass arguments we might be able to work around this by the following:
-- When a rewrite is applied to a term containing a typeclass argument (which we might be able to
-- track via e-class analysis), export that term, check if it's type correct, and if not,
-- try to resynthesize any contained typeclass instances. If this works reintroduce the typecorrect
-- term into the egraph.
-- How do we prove that this new term is equivalent to the old one though? Changing typeclass
-- instances isn't generally defeq.

-- Could it be that it is usually the case that if it makes sense to rewrite a dependent argument
-- by itself then its only dependents will be typeclass arguments (because otherwise the result
-- would need to involve a cast or something like that)?

-- Simp only somehow knows how to handle this:
set_option pp.explicit true in
theorem t : (if 0 = 0 then 0 else 1) = 0 := by
  have : (0 = 0) = True := eq_self 0
  simp only [this]
  sorry

-- Where does it pull `ite_congr` from? Does it have something to do with the `congr` attribute?
#print t
#check ite_congr
