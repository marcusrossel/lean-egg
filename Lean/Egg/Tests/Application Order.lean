import Egg

example (p q : Nat → Prop) : ((∀ x, p x) ∧ (∀ x, q x)) ↔ ∀ x, p x ∧ q x := by
  egg [forall_and]

example (p q : Nat → Nat → Prop) : ((∀ x, p 1 x) ∧ (∀ x, q 1 x)) ↔ ∀ x, p 1 x ∧ q 1 x := by
  egg [forall_and]

-- TODO: egg can't apply `forall_and`, because `p x 1` and `q x 1` are not syntactially of the form
--       `f x`. Of course we can write them in that form as `(fun a => p a 1) x`. How does `rw`
--       figure this out? Is it through `kabstract`?
example (p q : Nat → Nat → Prop) : ((∀ x, p x 1) ∧ (∀ x, q x 1)) ↔ ∀ x, p x 1 ∧ q x 1 := by
  sorry -- egg [forall_and]

example (p q : Nat → Nat → Prop) : ((∀ x, p x 1) ∧ (∀ x, q x 1)) ↔ ∀ x, p x 1 ∧ q x 1 := by
  egg [@forall_and _ (fun a => p a 1) (fun a => q a 1)]

example (p q : Nat → Nat → Prop) : ((∀ x, p x 1) ∧ (∀ x, q x 1)) ↔ ∀ x, p x 1 ∧ q x 1 := by
  rw [forall_and]
