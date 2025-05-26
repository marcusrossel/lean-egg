import Egg.Tactic.Trace
import Lean

open Lean Meta Elab Tactic

-- TODO: Perform pruning during generation, not after.

namespace Egg.Rewrites

def dup? (tgts : Rewrites) (rw : Rewrite) : MetaM (Option Source) := do
  let absRw ← abstractMVars (← mkEq rw.lhs rw.rhs)
  let conds ← rw.conds.mapM fun cond => AbstractMVarsResult.expr <$> abstractMVars (.mvar cond.mvar)
  for t in tgts do
    let absT ← abstractMVars (← mkEq t.lhs t.rhs)
    if absRw.expr != absT.expr then continue
    let tConds ← t.conds.mapM fun cond => AbstractMVarsResult.expr <$> abstractMVars (.mvar cond.mvar)
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
  | derived
  | structProj

private def RewriteCategory.title : RewriteCategory → String
  | .tagged     => "Tagged"
  | .intros     => "Intros"
  | .basic      => "Basic"
  | .builtins   => "Builtin"
  | .derived    => "Derived"
  | .structProj => "Structure Projections"

private structure State where
  all        : Rewrites
  pruned     : Rewrites.Pruned
  tagged     : Rewrites
  intros     : Rewrites
  basic      : Rewrites
  builtins   : Rewrites
  derived    : Rewrites
  structProj : Rewrites

private instance : EmptyCollection State where
  emptyCollection := {
    all        := #[]
    pruned     := {}
    tagged     := #[]
    intros     := #[]
    basic      := #[]
    builtins   := #[]
    derived    := #[]
    structProj := #[]
  }

private def State.get (s : State) : RewriteCategory → Rewrites
  | .tagged     => s.tagged
  | .intros     => s.basic
  | .basic      => s.basic
  | .builtins   => s.builtins
  | .derived    => s.derived
  | .structProj => s.structProj

private def State.set (s : State) : RewriteCategory → Rewrites → State
  | .tagged,     rws => { s with tagged     := rws }
  | .intros,     rws => { s with intros     := rws }
  | .basic,      rws => { s with basic      := rws }
  | .builtins,   rws => { s with builtins   := rws }
  | .derived,    rws => { s with derived    := rws }
  | .structProj, rws => { s with structProj := rws }

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

def generate' (cat : RewriteCategory) (conditionSubgoals : Bool) (g : GenM Premises) : GenM Unit := do
  let { rws := ⟨new, stxs⟩ } ← g
  let mut (new, stx) ← prune new (if stxs.isEmpty then none else stxs)
  let cls := `egg.rewrites
  withTraceNode cls (fun _ => return m!"{cat.title} ({new.size})") do new.trace stx cls conditionSubgoals
  set cat new
  addAll new

def generate (cat : RewriteCategory) (conditionSubgoals : Bool) (g : GenM Rewrites) : GenM Unit := do
  generate' cat conditionSubgoals do return { rws.elems := ← g, rws.stxs := #[] }
