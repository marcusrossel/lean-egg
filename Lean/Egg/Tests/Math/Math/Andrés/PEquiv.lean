import Egg
import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.SimpRw

namespace PEquiv

variable (p q : Prop) {α : Sort _} {β : Type _} (s : α → Prop)

theorem not_exists_eq : (¬ ∃ x, s x) = (∀ x, ¬ s x) := propext not_exists
theorem not_and_eq : (¬ (p ∧ q)) = (p → ¬ q) := propext not_and

structure PEquiv (α : Type u) (β : Type v) where
  /-- The underlying partial function of a `PEquiv` -/
  toFun : α → Option β
  /-- The partial inverse of `toFun` -/
  invFun : β → Option α
  /-- `invFun` is the partial inverse of `toFun`  -/
  inv : ∀ (a : α) (b : β), a ∈ invFun b ↔ b ∈ toFun a

/-- A `PEquiv` is a partial equivalence, a representation of a bijection between a subset
  of `α` and a subset of `β`. See also `PartialEquiv` for a version that requires `toFun` and
`invFun` to be globally defined functions and has `source` and `target` sets as extra fields. -/
infixr:25 " ≃. " => PEquiv

namespace PEquiv

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

open Function Option

/-- The identity map as a partial equivalence. -/
@[refl]
protected def refl (α : Type _) : α ≃. α where
  toFun := some
  invFun := some
  inv _ _ := eq_comm

/-- The inverse partial equivalence. -/
@[symm]
protected def symm (f : α ≃. β) : β ≃. α where
  toFun := f.2
  invFun := f.1
  inv _ _ := (f.inv _ _).symm

theorem mem_iff_mem (f : α ≃. β) : ∀ {a : α} {b : β}, a ∈ f.symm.toFun b ↔ b ∈ f.toFun a :=
  f.3 _ _

theorem eq_some_iff (f : α ≃. β) : ∀ {a : α} {b : β}, f.symm.toFun b = some a ↔ f.toFun a = some b :=
  f.3 _ _

/-- Composition of partial equivalences `f : α ≃. β` and `g : β ≃. γ`. -/
protected def trans (f : α ≃. β) (g : β ≃. γ) :
    α ≃. γ where
  toFun a := (f.toFun a).bind g.toFun
  invFun a := (g.symm.toFun a).bind f.symm.toFun
  inv a b := by simp_all [and_comm, eq_some_iff f, eq_some_iff g, bind_eq_some]

@[simp]
theorem refl_apply (a : α) : (PEquiv.refl α).toFun a = some a :=
  rfl

@[simp]
theorem symm_refl : (PEquiv.refl α).symm = PEquiv.refl α :=
  rfl

theorem Option.bind_eq_some' {x : Option α} {f : α → Option β} {b : β} :
    x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp

theorem mem_trans (f : α ≃. β) (g : β ≃. γ) (a : α) (c : γ) :
    c ∈ (f.trans g).toFun a ↔ ∃ b, b ∈ f.toFun a ∧ c ∈ g.toFun b :=
  Option.bind_eq_some'

theorem Decidable.not_or_of_imp [inst : Decidable a] (h : a → b) : ¬a ∨ b :=
  if ha : a then .inr (h ha) else .inl ha

theorem Decidable.imp_iff_not_or [inst : Decidable a] : (a → b) ↔ (¬a ∨ b) :=
  ⟨not_or_of_imp, Or.neg_resolve_left⟩

theorem imp_iff_not_or : a → b ↔ ¬a ∨ b := Decidable.imp_iff_not_or (inst := Classical.propDecidable a)

theorem forall_swap {p : α → β → Prop} : (∀ x y, p x y) ↔ ∀ y x, p x y :=
  ⟨fun f x y ↦ f y x, fun f x y ↦ f y x⟩

example (f : α ≃. β) (g : β ≃. γ) (a : α) : (f.trans g).toFun a = none ↔ ∀ b c, b ∉ f.toFun a ∨ c ∉ g.toFun b := by
  simp only [eq_none_iff_forall_not_mem, mem_trans, imp_iff_not_or.symm]
  simp_rw [Mathlib.Tactic.PushNeg.not_exists_eq, Mathlib.Tactic.PushNeg.not_and_eq]
  rw [forall_swap]

example (f : α ≃. β) (g : β ≃. γ) (a : α) : (f.trans g).toFun a = none ↔ ∀ b c, b ∉ f.toFun a ∨ c ∉ g.toFun b := by
  simp_rw [eq_none_iff_forall_not_mem, mem_trans, imp_iff_not_or.symm,
           Mathlib.Tactic.PushNeg.not_exists_eq, Mathlib.Tactic.PushNeg.not_and_eq]
  rw [forall_swap]

--set_option egg.timeLimit 20
set_option egg.reporting true

example (f : α ≃. β) (g : β ≃. γ) (a : α) : (f.trans g).toFun a = none ↔ ∀ b c, b ∉ f.toFun a ∨ c ∉ g.toFun b := by
  simp only [eq_none_iff_forall_not_mem, mem_trans, imp_iff_not_or.symm]
  egg [
    forall_swap, not_exists_eq,
    not_and_eq
  ]
  sorry

  --push_neg
  --exact forall_swap

  -- egg [
  --   Option.eq_none_iff_forall_not_mem, mem_trans, imp_iff_not_or.symm, forall_swap, not_exists_eq,
  --   not_and_eq
  -- ]

set_option egg.slotted true in
example (f : α ≃. β) (g : β ≃. γ) (a : α) : (f.trans g).toFun a = none ↔ ∀ b c, b ∉ f.toFun a ∨ c ∉ g.toFun b := by
  simp only [eq_none_iff_forall_not_mem, mem_trans, imp_iff_not_or.symm]
  egg [
    forall_swap, not_exists_eq,
    not_and_eq
  ]

  -- egg [
  --   Option.eq_none_iff_forall_not_mem, mem_trans, imp_iff_not_or.symm, forall_swap, not_exists_eq,
  --   not_and_eq
  -- ]

end PEquiv
