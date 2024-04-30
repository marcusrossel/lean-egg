import Egg

-- This fails because we're lacking universe level defeqs.
set_option trace.egg true in
example (h : ∀ γ : Sort (max u v), γ = id γ) (α : Sort (u + 1)) (β : Sort (v + 1)) : (α × β) = id (α × β) := by
  egg [h]

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


theorem thm₂ : ∀ x : Nat, (fun _ => (fun _ => x) x) 0 = x := fun _ => rfl

-- This seems to cause an infinite loop or at least extremely long runtime in
-- `correct_bvar_indices` or `subst`. I think what is happening is that `thm₂` is applied in
-- the backward direction over and over again which quickly blows up the e-graph.
-- Investigate further what's happening by somehow tracing `correct_bvar_indices`.
set_option egg.shiftCapturedBVars true in
example : True := by
  have : (fun x => (fun a => (fun a => a) a) 0) = (fun x => x) := by sorry -- egg [thm₂]
  constructor
