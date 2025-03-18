import Egg
import Mathlib.RingTheory.PrimeSpectrum
import Mathlib.Algebra.Module.LocalizedModule
import Mathlib.RingTheory.Localization.AtPrime

attribute [egg neg] Mathlib.Tactic.PushNeg.not_not_eq
attribute [egg neg] Mathlib.Tactic.PushNeg.not_and_eq
attribute [egg neg] Mathlib.Tactic.PushNeg.not_and_or_eq
attribute [egg neg] Mathlib.Tactic.PushNeg.not_or_eq
attribute [egg neg] Mathlib.Tactic.PushNeg.not_forall_eq
attribute [egg neg] Mathlib.Tactic.PushNeg.not_exists_eq
attribute [egg neg] Mathlib.Tactic.PushNeg.not_implies_eq
attribute [egg neg] Mathlib.Tactic.PushNeg.not_ne_eq
attribute [egg neg] Mathlib.Tactic.PushNeg.not_iff
attribute [egg neg] Mathlib.Tactic.PushNeg.not_nonempty_eq
attribute [egg neg] Mathlib.Tactic.PushNeg.ne_empty_eq_nonempty
attribute [egg neg] Mathlib.Tactic.PushNeg.empty_ne_eq_nonempty

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {p : PrimeSpectrum R}

variable (R M) in
/-- The support of a module, defined as the set of primes `p` such that `Mₚ ≠ 0`. -/
def Module.support : Set (PrimeSpectrum R) :=
  { p | Nontrivial (LocalizedModule p.asIdeal.primeCompl M) }

lemma Module.mem_support_iff :
    p ∈ Module.support R M ↔ Nontrivial (LocalizedModule p.asIdeal.primeCompl M) := Iff.rfl

lemma Module.not_mem_support_iff :
    p ∉ Module.support R M ↔ Subsingleton (LocalizedModule p.asIdeal.primeCompl M) :=
  not_nontrivial_iff_subsingleton

lemma Module.not_mem_support_iff' :
    p ∉ Module.support R M ↔ ∀ m : M, ∃ r ∉ p.asIdeal, r • m = 0 := by
   egg [not_mem_support_iff, LocalizedModule.subsingleton_iff]
  --rw [not_mem_support_iff, LocalizedModule.subsingleton_iff]
  --rfl

set_option egg.timeLimit 100 in
set_option egg.slotted true in
set_option egg.reporting true in
lemma Module.mem_support_iff' :
    p ∈ Module.support R M ↔ ∃ m : M, ∀ r ∉ p.asIdeal, r • m ≠ 0 := by
  -- inifinite loop?
  egg neg [not_not , not_mem_support_iff']
  --rw [← @not_not (_ ∈ _), not_mem_support_iff']
  --push_neg
  --rfl
