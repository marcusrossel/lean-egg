import Egg.Core.Gen.TcProjs
import Egg.Core.Gen.TcSpecs
import Egg.Core.Gen.GoalTcSpecs
import Egg.Core.Gen.GoalTypeSpecialization
import Egg.Core.Gen.Explosion
import Lean

open Lean Std Meta Elab Tactic

namespace Egg.Premises.DerivedM

private inductive DerivationCategory where
  | tcProj
  | tcSpec
  | goalTcSpec
  | goalTypeSpec
  | explosion

private def DerivationCategory.all : Array DerivationCategory :=
  #[tcProj, tcSpec, goalTcSpec, goalTypeSpec, explosion]

-- We maintain this theorem to ensure that we don't forget to add elements to
-- `DerivationCategory.all`.
theorem DerivationCategory.all_complete (c : DerivationCategory) : c ∈ all := by
  cases c <;> simp [all]

private def DerivationCategory.isEnabled (cfg : Config.Gen): DerivationCategory → Bool
  | tcProj       => cfg.genTcProjRws
  | tcSpec       => cfg.genTcSpecRws
  | goalTcSpec   => cfg.genGoalTcSpec
  | goalTypeSpec => cfg.genGoalTypeSpec
  | explosion    => cfg.explosion

-- Each index in this structure indicates to which point in `State.derived` a given derivation
-- category has been applied. More precisely, these indices indicate the first element that has not
-- been considered yet.
private structure State.Progress where
  tcProj       : Nat
  tcSpec       : Nat
  goalTcSpec   : Nat
  goalTypeSpec : Nat
  explosion    : Nat

private def State.Progress.get (p : Progress) : DerivationCategory → Nat
  | .tcProj       => p.tcProj
  | .tcSpec       => p.tcSpec
  | .goalTcSpec   => p.goalTcSpec
  | .goalTypeSpec => p.goalTypeSpec
  | .explosion    => p.explosion

private def State.Progress.set (p : Progress) : DerivationCategory → Nat → Progress
  | .tcProj,       n => { p with tcProj       := n }
  | .tcSpec,       n => { p with tcSpec       := n }
  | .goalTcSpec,   n => { p with goalTcSpec   := n }
  | .goalTypeSpec, n => { p with goalTypeSpec := n }
  | .explosion,    n => { p with explosion    := n }

private structure State where
  derived     : Rewrites
  progress    : State.Progress
  tcProjCover : HashSet TcProj

private instance : EmptyCollection State where
  emptyCollection := {
    derived     := #[]
    progress    := ⟨0, 0, 0, 0, 0⟩
    tcProjCover := ∅
  }

private abbrev _root_.Egg.Premises.DerivedM := StateT State TacticM

nonrec def run (m : DerivedM Unit) : TacticM Rewrites := do
  let { derived, .. } ← Prod.snd <$> m.run ∅
  return derived

private def tcProjCover : DerivedM (HashSet TcProj) :=
  return (← get).tcProjCover

private def isDone (cfg : Config) : DerivedM Bool := do
  let { derived, progress, .. } ← get
  return DerivationCategory.all.all fun cat =>
    !cat.isEnabled cfg || (progress.get cat) >= derived.size

private def add' (cat? : Option DerivationCategory) (rws : Rewrites) : DerivedM Unit := do
  modify fun s => { s with derived  := s.derived ++ rws }
  let some cat := cat? | return
  modify fun s => { s with progress := s.progress.set cat s.derived.size }

private def add (cat : DerivationCategory) (rws : Rewrites) : DerivedM Unit :=
  add' cat rws

private def setTcProjCover (tcProjCover : HashSet TcProj) : DerivedM Unit :=
  modify ({ · with tcProjCover })

private def todo (cat : DerivationCategory) : DerivedM Rewrites := do
  let { derived, progress, .. } ← get
  return derived[(progress.get cat):]

private def generate
    (cfg : Config.Gen) (cat : DerivationCategory) (m : DerivedM Rewrites) : DerivedM Unit := do
  if cat.isEnabled cfg then add cat (← m)

end DerivedM

open DerivedM

-- TODO: We need to be careful about making sure that we don't loop infinitely.
--       For example, tc proj and explosion might easily loop.
partial def genDerived (goal : Congr) (rws : Rewrites) (guides : Guides) (cfg : Config) :
    TacticM Rewrites := do
  let all ← DerivedM.run do
    add' (cat? := none) rws
    addInitialTcProjs
    while !(← isDone cfg) do core
  return all[rws.size:]
where
  addInitialTcProjs : DerivedM Unit := do
    unless cfg.genTcProjRws do return
    let targets := rws.tcProjTargets ++ goal.tcProjTargets .goal ++ guides.tcProjTargets
    let (rws, cover) ← genTcProjReductions targets (covered := ∅) cfg
    add .tcProj rws
    setTcProjCover cover

  core : DerivedM Unit := do
    generate cfg .explosion do
      genExplosions (← todo .explosion)
    generate cfg .goalTypeSpec do
      genGoalTypeSpecializations (← todo .goalTypeSpec) goal cfg.conditionSubgoals
    generate cfg .goalTcSpec do
      genGoalTcSpecializations (← todo .goalTcSpec) cfg.toNormalization cfg.conditionSubgoals goal
    generate cfg .tcSpec do
      genTcSpecializations (← todo .tcSpec) cfg.toNormalization cfg.conditionSubgoals
    generate cfg .tcProj do
      let targets := (← todo .tcProj).tcProjTargets
      let (rws, cover) ← genTcProjReductions targets (← tcProjCover) cfg
      setTcProjCover cover
      return rws
