import Egg

-- Tests for manually inspecting what terms look like with type tags and universe levels.
set_option trace.egg true

private def h₁ : ∀ (a : Bool) (b : Nat), (a, b).fst = a := fun _ _ => rfl
private def h₂ : ∀ (a : Bool) (b : Nat), (b, a).snd = a := fun _ _ => rfl

example (a : Bool) (b : Nat) : (a, b).fst = (b, a).snd := by
  egg (config := { typeTags := .none, eraseULvls := true }) [h₁, h₂]

example (a : Bool) (b : Nat) : (a, b).fst = (b, a).snd := by
  egg (config := { typeTags := .none, eraseULvls := false }) [h₁, h₂]

-- TODO: These cases fail as proof reconstruction can't handle type tags yet.

example (a : Bool) (b : Nat) : (a, b).fst = (b, a).snd := by
  egg (config := { typeTags := .indices, eraseULvls := true }) [h₁, h₂]

example (a : Bool) (b : Nat) : (a, b).fst = (b, a).snd := by
  egg (config := { typeTags := .indices, eraseULvls := false }) [h₁, h₂]

example (a : Bool) (b : Nat) : (a, b).fst = (b, a).snd := by
  egg (config := { typeTags := .exprs, eraseULvls := true }) [h₁, h₂]

example (a : Bool) (b : Nat) : (a, b).fst = (b, a).snd := by
  egg (config := { typeTags := .exprs, eraseULvls := false }) [h₁, h₂]
