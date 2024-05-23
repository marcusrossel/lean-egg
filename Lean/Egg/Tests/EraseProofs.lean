import Egg

-- Tests for manually inspecting what terms look like with or without proof erasure.

set_option egg.eraseProofs true

set_option egg.eraseProofs false in
example (i : Nat) (h : i < 10) : (Fin.mk i h).val = i := by
  have : ∀ n m (g : n < m), (Fin.mk n g).val = n := by simp
  egg [this]

example (i : Nat) (h : i < 10) : (Fin.mk i h).val = i := by
  have : ∀ n m (g : n < m), (Fin.mk n g).val = n := by simp
  egg [this]

example (i : Nat) (h : ∀ i : Nat, i < 10) : (Fin.mk i (h i)).val = i := by
  have : ∀ n m (g : n < m), (Fin.mk n g).val = n := by simp
  egg [this]

-- The following test is an attempt to construct a rewrite where the mvar `x` does appear in the
-- proof term on the rhs, but not in the *type* of the proof term. If this succeeded, proof erasure
-- should cause a crash during variable substitution after e-matching, as proofs are encoded by
-- their type, which is therefore missing the mvar for `x`. But obviously, the rewrite `h` does not
-- achieve this yet.
example (h : ∀ x : Nat, x = Exists.choose (Exists.intro x x.zero_le)) : True = True := by
  egg [h]

/-- error: egg failed to prove goal -/
#guard_msgs in
set_option egg.eraseProofs false in
example
    (f : (a b : Nat) → a > b → Nat) (g : Nat → Nat) (a₁ a₂ b₁ b₂ c d : Nat) (h₁ : a₁ > b₁)
    (h₂ : a₂ > b₂) (h₃ : a₁ = c) (h₄ : a₂ = c) (h₅ : b₁ = d) (h₆ : d = b₂) :
    g (g (f a₁ b₁ h₁)) = g (g (f a₂ b₂ h₂)) := by
  egg [*]

-- TODO: We don't currently support rewriting the types of proof terms. I think this shouldn't be
--       too difficult to support though.
/-- error: egg failed to parse explanation: step contains type-level rewrite in proof -/
#guard_msgs in
set_option egg.eraseProofs true in
example
    (f : (a b : Nat) → a > b → Nat) (g : Nat → Nat) (a₁ a₂ b₁ b₂ c d : Nat) (h₁ : a₁ > b₁)
    (h₂ : a₂ > b₂) (h₃ : a₁ = c) (h₄ : a₂ = c) (h₅ : b₁ = d) (h₆ : d = b₂) :
    g (g (f a₁ b₁ h₁)) = g (g (f a₂ b₂ h₂)) := by
  egg [*]
