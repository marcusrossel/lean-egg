import Egg.Core.Rewrite.Basic

open Lean Std

namespace Egg.Rewrite

structure Rule.Id where
  src : Source
  dir : Direction
deriving Inhabited, BEq, Hashable, Ord, Repr

-- TODO: We are currently ordering `Source`s by their string description. Other orderings (e.g. by
--       category may be nicer for tracing).
instance : LT Rule.Id := Ord.toLT inferInstance

def Rule.Id.description (id : Rule.Id) : String :=
  s!"{id.dir.description}{id.src.description}"

-- A `Rewrite.Rule` is a `Rewrite` with an identity.
structure Rule where
  id : Rule.Id
  rw : Rewrite

def «with» (rw : Rewrite) (src : Source) (dir : Direction) : Rule :=
  { id.src := src, id.dir := dir, rw }

namespace Rule

def src (rule : Rule) : Source :=
  rule.id.src

def dir (rule : Rule) : Direction :=
  rule.id.dir

def from?
    (src : Source) (dir : Direction) (proof type : Expr) (cfg : Config.Normalization)
    (normalize := true) : MetaM (Option Rule) := do
  let some rw ← Rewrite.from? dir proof type cfg normalize | return none
  return some { id.src := src, id.dir := dir, rw }

def both? (src : Source) (proof type : Expr) (cfg : Config.Normalization) (normalize := true) :
    MetaM <| Option (Rule × Rule) := do
  let some (fwd, bwd) ← Rewrite.both? proof type cfg normalize | return none
  let fwd := { id.src := src, id.dir := .forward,  rw := fwd }
  let bwd := { id.src := src, id.dir := .backward, rw := bwd }
  return some (fwd, bwd)

def ground? (src : Source) (proof type : Expr) (cfg : Config.Normalization) (normalize := true) :
    MetaM (Option Rule) := do
  let some gnd ← Rewrite.ground? proof type cfg normalize | return none
  -- We arbitrarily choose the `.forward` direction.
  return some { id.src := src, id.dir := .forward, rw := gnd }

end Rule

structure Rules where
  rws  : HashMap Rule.Id Rewrite
  stxs : HashMap Source Syntax
deriving Inhabited

namespace Rules

instance : EmptyCollection Rules where
  emptyCollection := { rws := ∅, stxs := ∅ }

instance : Singleton Rule Rules where
  singleton rule := { rws := {(rule.id, rule.rw)}, stxs := ∅ }

def entries (rules : Rules) : Array Rule :=
  rules.rws.toArray
    |>.insertionSort (·.fst < ·.fst)
    |>.map fun (id, rw) => { id, rw }

def insert (rules : Rules) (rule : Rule) (stx? : Option Syntax := none) : Rules := Id.run do
  let (false, rws) := rules.rws.containsThenInsert rule.id rule.rw
    | panic! "egg: internal error, trying to insert a rewrite rule that already exists"
  let stxs :=
    match stx? with
    | none => rules.stxs
    | some stx => rules.stxs.insert rule.src stx
  return { rws, stxs }

-- Note: We use `Rules.insert` to get its duplication checking behaviour.
def union (rules₁ rules₂ : Rules) : Rules := Id.run do
  let mut rules := rules₁
  for (id, rw) in rules₂.rws do
    rules := rules.insert ⟨id, rw⟩ rules₂.stxs[id.src]?
  return rules

instance : Union Rules where
  union := .union

inductive AddConfig where
  | both
  | dir (d : Direction)
  | ground

def add?
    (rules : Rules) (src : Source) (proof type : Expr) (cfg : Config.Normalization)
    (addCfg : AddConfig := .both) (stx? : Option Syntax := none) (normalize := true) :
    MetaM (Option Rules) := do
  match addCfg with
  | .both =>
    let some (rule₁, rule₂) ← Rule.both? src proof type cfg normalize | return none
    return rules |>.insert rule₁ stx? |>.insert rule₂ stx?
  | .dir dir =>
    let some rule ← Rule.from? src dir proof type cfg normalize | return none
    return rules.insert rule stx?
  | .ground =>
    let some rule ← Rule.ground? src proof type cfg normalize | return none
    return rules.insert rule stx?

def filter (rules : Rules) (keep : Source → Bool) : Rules where
  rws  := rules.rws.filter  fun id  _ => keep id.src
  stxs := rules.stxs.filter fun src _ => keep src
