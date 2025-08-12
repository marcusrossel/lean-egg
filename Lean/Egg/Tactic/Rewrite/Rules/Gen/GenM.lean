import Egg.Tactic.Trace

open Lean Std Meta Elab Tactic

-- TODO: Perform pruning during generation, not after.

namespace Egg.Rewrite.Rules

def dup? (tgts : Rules) (rw : Rewrite) : MetaM (Option Source) := do
  let absRw ← abstractMVars (← mkEq rw.lhs rw.rhs)
  let conds ← rw.conds.active.mapM fun cond => AbstractMVarsResult.expr <$> abstractMVars (.mvar cond.mvar)
  for t in tgts.entries do
    let absT ← abstractMVars (← mkEq t.rw.lhs t.rw.rhs)
    if absRw.expr != absT.expr then continue
    let tConds ← t.rw.conds.active.mapM fun cond => AbstractMVarsResult.expr <$> abstractMVars (.mvar cond.mvar)
    if conds != tConds then continue
    return t.src
  return none

structure Pruned where
  rules   : Rewrite.Rules := ∅
  reasons : HashMap Rewrite.Rule.Id Source := ∅

def Pruned.insert (p : Pruned) (rule : Rule) (reason : Source) : Pruned where
  rules   := p.rules.insert rule
  reasons := p.reasons.insert rule.id reason

def Pruned.union (p₁ p₂ : Pruned) : Pruned where
  rules   := p₁.rules ∪ p₂.rules
  reasons := p₁.reasons ∪ p₂.reasons

instance : Union Pruned where
  union := .union

namespace GenM

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
  all          : Rules
  pruned       : Pruned
  tagged       : Rules
  intros       : Rules
  basic        : Rules
  builtins     : Rules
  goalTypeSpec : Rules
  explosion    : Rules
  tcProj       : Rules
  structProj   : Rules

private instance : EmptyCollection State where
  emptyCollection := {
    all          := ∅
    pruned       := {}
    tagged       := ∅
    intros       := ∅
    basic        := ∅
    builtins     := ∅
    goalTypeSpec := ∅
    explosion    := ∅
    tcProj       := ∅
    structProj   := ∅
  }

private def State.get (s : State) : RewriteCategory → Rules
  | .tagged       => s.tagged
  | .intros       => s.basic
  | .basic        => s.basic
  | .builtins     => s.builtins
  | .goalTypeSpec => s.goalTypeSpec
  | .explosion    => s.explosion
  | .tcProj       => s.tcProj
  | .structProj   => s.structProj

private def State.set (s : State) : RewriteCategory → Rules → State
  | .tagged,       rules => { s with tagged       := rules }
  | .intros,       rules => { s with intros       := rules }
  | .basic,        rules => { s with basic        := rules }
  | .builtins,     rules => { s with builtins     := rules }
  | .goalTypeSpec, rules => { s with goalTypeSpec := rules }
  | .explosion,    rules => { s with explosion    := rules }
  | .tcProj,       rules => { s with tcProj       := rules }
  | .structProj,   rules => { s with structProj   := rules }

abbrev _root_.Egg.Rewrite.Rules.GenM := StateT State TacticM

structure Result where
  all    : Rules
  pruned : Pruned

nonrec def run (m : GenM Unit) : TacticM Result := do
  let { all, pruned, .. } ← Prod.snd <$> m.run ∅
  return { all, pruned }

def all : GenM Rules :=
  return (← get).all

def allExceptGeneratedGroundEqs : GenM Rules :=
  return (← all).filter (!·.isGround)

private def addAll (new : Rules) : GenM Unit :=
  modify fun s => { s with all := s.all ∪ new }

private def addPruned (new : Pruned) : GenM Unit :=
  modify fun s => { s with pruned := s.pruned ∪ new }

def set (cat : RewriteCategory) (rules : Rules) : GenM Unit :=
  modify (·.set cat rules)

nonrec def get (cat : RewriteCategory) : GenM Rules :=
  return (← get).get cat

private def prune (rules : Rules) : GenM Rules := do
  let mut keep := ∅
  let mut pruned := {}
  for rule in rules.entries do
    if let some dup ← keep.dup? rule.rw then
      pruned := pruned.insert rule dup
    else if let some dup ← (← all).dup? rule.rw then
      pruned := pruned.insert rule dup
    else
      keep := keep.insert rule rules.stxs[rule.src]?
  addPruned pruned
  return keep

def generate (cat : RewriteCategory) (cfg : Config) (g : GenM Rules) : GenM Unit := do
  unless cat.isEnabled cfg do return
  let mut new ← g
  new ← prune new
  withTraceNode cat.traceClass (fun _ => return m!"{cat.title} ({new.rws.size})") do
    new.trace cat.traceClass cfg.subgoals
  set cat new
  addAll new
