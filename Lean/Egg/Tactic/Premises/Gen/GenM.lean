import Egg.Tactic.Trace
import Lean

open Lean Meta Elab Tactic

-- TODO: Perform pruning during generation, not after.

namespace Egg.Rewrites

def dup? (tgts : Rewrites) (rw : Rewrite) : MetaM (Option Source) := do
  let absRw ← abstractMVars (← mkEq rw.lhs rw.rhs)
  let conds ← rw.conds.active.mapM fun cond => AbstractMVarsResult.expr <$> abstractMVars (.mvar cond.mvar)
  for t in tgts do
    let absT ← abstractMVars (← mkEq t.lhs t.rhs)
    if absRw.expr != absT.expr then continue
    let tConds ← t.conds.active.mapM fun cond => AbstractMVarsResult.expr <$> abstractMVars (.mvar cond.mvar)
    if conds != tConds then continue
    return t.src
  return none

structure Pruned where
  rws     : Rewrites := #[]
  reasons : Array Source := #[]

def Pruned.push (p : Rewrites.Pruned) (rw : Rewrite) (reason : Source) : Rewrites.Pruned where
  rws     := p.rws.push rw
  reasons := p.reasons.push reason

instance : Append Rewrites.Pruned where
  append p₁ p₂ := {
    rws     := p₁.rws ++ p₂.rws
    reasons := p₁.reasons ++ p₂.reasons
  }

end Rewrites

namespace Premises.GenM

private inductive RewriteCategory where
  | tagged
  | intros
  | basic
  | builtins
  | goalTypeSpec
  | explosion
  | tcProj
  | structProj

namespace RewriteCategory

private def title : RewriteCategory → String
  | .tagged       => "Tagged"
  | .intros       => "Intros"
  | .basic        => "Basic"
  | .builtins     => "Builtin"
  | .goalTypeSpec => "Goal Type Specialization"
  | .explosion    => "Explosion"
  | .tcProj       => "Type Class Projections"
  | .structProj   => "Structure Projections"

private def traceClass : RewriteCategory → Name
  | .tagged       => `egg.rewrites.baskets
  | .intros       => `egg.rewrites.intro
  | .basic        => `egg.rewrites.explicit
  | .builtins     => `egg.rewrites.builtin
  | .goalTypeSpec => `egg.rewrites.goalTypeSpec
  | .explosion    => `egg.rewrites.explosion
  | .tcProj       => `egg.rewrites.tcProj
  | .structProj   => `egg.rewrites.structProj

private def isEnabled (cfg : Config.Gen) : RewriteCategory → Bool
  | .tagged | .intros | .basic => true
  | .builtins                  => cfg.builtins
  | .goalTypeSpec              => cfg.goalTypeSpec
  | .explosion                 => cfg.explosion
  | .tcProj                    => cfg.tcProjs
  | .structProj                => cfg.structProjs

end RewriteCategory

private structure State where
  all          : Rewrites
  pruned       : Rewrites.Pruned
  tagged       : Rewrites
  intros       : Rewrites
  basic        : Rewrites
  builtins     : Rewrites
  goalTypeSpec : Rewrites
  explosion    : Rewrites
  tcProj       : Rewrites
  structProj   : Rewrites

private instance : EmptyCollection State where
  emptyCollection := {
    all          := #[]
    pruned       := {}
    tagged       := #[]
    intros       := #[]
    basic        := #[]
    builtins     := #[]
    goalTypeSpec := #[]
    explosion    := #[]
    tcProj       := #[]
    structProj   := #[]
  }

private def State.get (s : State) : RewriteCategory → Rewrites
  | .tagged       => s.tagged
  | .intros       => s.basic
  | .basic        => s.basic
  | .builtins     => s.builtins
  | .goalTypeSpec => s.goalTypeSpec
  | .explosion    => s.explosion
  | .tcProj       => s.tcProj
  | .structProj   => s.structProj

private def State.set (s : State) : RewriteCategory → Rewrites → State
  | .tagged,       rws => { s with tagged       := rws }
  | .intros,       rws => { s with intros       := rws }
  | .basic,        rws => { s with basic        := rws }
  | .builtins,     rws => { s with builtins     := rws }
  | .goalTypeSpec, rws => { s with goalTypeSpec := rws }
  | .explosion,    rws => { s with explosion    := rws }
  | .tcProj,       rws => { s with tcProj       := rws }
  | .structProj,   rws => { s with structProj   := rws }

abbrev _root_.Egg.Premises.GenM := StateT State TacticM

structure Result where
  all    : Rewrites
  pruned : Rewrites.Pruned

nonrec def run (m : GenM Unit) : TacticM Result := do
  let { all, pruned, .. } ← Prod.snd <$> m.run ∅
  return { all, pruned }

def all : GenM Rewrites :=
  return (← get).all

def allExceptGeneratedGroundEqs : GenM Rewrites :=
  return (← all).filter (!·.src.isGround)

private def addAll (new : Rewrites) : GenM Unit := do
  modify fun s => { s with all := s.all ++ new }

private def addPruned (new : Rewrites.Pruned) : GenM Unit := do
  modify fun s => { s with pruned := s.pruned ++ new }

def set (cat : RewriteCategory) (rws : Rewrites) : GenM Unit :=
  modify (·.set cat rws)

nonrec def get (cat : RewriteCategory) : GenM Rewrites :=
  return (← get).get cat

private def prune (rws : Rewrites) (stx? : Option (Array Syntax) := none) :
    GenM (Rewrites × Array Syntax) := do
  let mut keep : Rewrites := #[]
  let mut keepStx := #[]
  let mut pruned := {}
  for rw in rws, idx in [:rws.size] do
    if let some dup ← keep.dup? rw then
      pruned := pruned.push rw dup
    else if let some dup ← (← all).dup? rw then
      pruned := pruned.push rw dup
    else
      keep := keep.push rw
      if let some stx := stx? then keepStx := keepStx.push stx[idx]!
  addPruned pruned
  return (keep, keepStx)

def generate' (cat : RewriteCategory) (cfg : Config) (g : GenM Premises) : GenM Unit := do
  unless cat.isEnabled cfg do return
  let { rws := ⟨new, stxs⟩ } ← g
  let mut (new, stx) ← prune new (if stxs.isEmpty then none else stxs)
  withTraceNode cat.traceClass (fun _ => return m!"{cat.title} ({new.size})") do
    new.trace stx cat.traceClass cfg.subgoals
  set cat new
  addAll new

def generate (cat : RewriteCategory) (cfg : Config) (g : GenM Rewrites) : GenM Unit := do
  generate' cat cfg do return { rws.elems := ← g, rws.stxs := #[] }
