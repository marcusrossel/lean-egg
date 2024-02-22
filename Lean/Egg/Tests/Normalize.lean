import Egg

-- This tests that `Egg.normalize` doesn't introduce loose fvars.

variable {I : Type u} {f : I → Type v₁} (x y : (i : I) → f i) (i : I)

instance instMul [∀ i, Mul <| f i] : Mul (∀ i : I, f i) :=
  ⟨fun f g i => f i * g i⟩

theorem mul_apply [∀ i, Mul <| f i] : (x * y) i = x i * y i :=
  rfl

example : True = True := by
  egg [mul_apply]
