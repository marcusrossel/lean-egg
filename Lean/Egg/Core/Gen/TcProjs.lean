import Egg.Core.Rewrite.Basic
import Egg.Core.Guides
import Lean

open Lean Std Meta

namespace Egg

structure TcProjTarget where
  expr : Expr
  src  : Source
  loc  : Source.TcProjLocation

def Congr.tcProjTargets (cgr : Congr) (src : Source) : Array TcProjTarget := #[
  { expr := cgr.lhs, src, loc := .left },
  { expr := cgr.rhs, src, loc := .right }
]

def Rewrites.tcProjTargets (rws : Rewrites) : Array TcProjTarget := Id.run do
  let mut sources : Array TcProjTarget := #[]
  for rw in rws do
    sources := sources ++ rw.toCongr.tcProjTargets rw.src
    for cond in rw.conds.active, idx in [:rw.conds.active.size] do
      sources := sources.push { expr := cond.type, src := rw.src, loc := .cond idx }
  return sources

def Guides.tcProjTargets (guides : Guides) : Array TcProjTarget :=
  guides.map fun guide => { expr := guide.expr, src := guide.src, loc := .root }

private structure SourcePrefix where
  src : Source
  loc : Source.TcProjLocation
  pos : SubExpr.Pos

section TcProjs

private abbrev TcProjs := ExprMap SourcePrefix

private structure State where
  projs : TcProjs     := ∅
  args  : Array Expr  := #[]
  pos   : SubExpr.Pos := .root
  src   : Source
  loc   : Source.TcProjLocation
  deriving Inhabited

/- TODO: Use a monad for this.

private structure CollectionM.State where
  projs : TcProjs     := ∅
  args  : Array Expr  := #[]
  pos   : SubExpr.Pos := .root
  deriving Inhabited

private abbrev CollectionM := StateT CollectionM.State MetaM

namespace CollectionM

private def withContext
    (args : Array Expr → Array Expr) (pos : SubExpr.Pos → SubExpr.Pos) (m : CollectionM α) :
    CollectionM α := do
  let before ← getModify fun s => { s with args := args s.args, pos := pos s.pos }
  let result ← m
  set before
  return result

private def underBindingDomain (m : CollectionM α) : CollectionM α := do
  withContext (fun _ => #[]) (·.pushBindingDomain) m

private def underBindingBody (m : CollectionM α) : CollectionM α := do
  withContext (fun _ => #[]) (·.pushBindingBody) m
-/

private partial def TcProjs.from (targets : Array TcProjTarget) : MetaM TcProjs := do
  -- Note: These initial values are dummy values which are properly set before first use.
  let mut state := { src := .goal, loc := .root }
  for { expr, src, loc } in targets do
    state ← go expr { state with src, loc }
  return state.projs
where
  go : Expr → State → MetaM State
    | .const c lvls                   => visitConst c lvls
    | .app fn arg                     => (visitFn fn arg) >=> (visitArg arg)
    | .lam _ d b _ | .forallE _ d b _ => (visitBindingDomain d) >=> (visitBindingBody b)
    | .mdata .. | .proj .. | .letE .. => fun _ => throwError "egg: internal error: 'Egg.tcProjs.go' received non-normalized expression"
    | _                               => pure

  visitConst (const : Name) (lvls : List Level) (s : State) : MetaM State := do
    let some info ← getProjectionFnInfo? const | return s
    unless info.fromClass && s.args.size > info.numParams do return s
    let args := s.args[:info.numParams + 1].toArray
    -- TODO: reconsider these constraints for "TC Proj Binders.lean" and "TC Diamonds.lean".
    if args.back!.isMVar || args.any (·.hasLooseBVars) then return s
    let proj := mkAppN (.const const lvls) args
    return { s with projs := s.projs.insert proj { src := s.src, loc := s.loc, pos := s.pos } }

  visitBindingDomain (d : Expr) (s : State) : MetaM State := do
    let s' ← go d { s with args := #[], pos := s.pos.pushBindingDomain }
    return { s' with pos := s.pos }

  visitBindingBody (b : Expr) (s : State) : MetaM State := do
    let s' ← go b { s with args := #[], pos := s.pos.pushBindingBody }
    return { s' with pos := s.pos }

  visitFn (fn : Expr) (arg : Expr) (s : State) : MetaM State := do
    let s' ← go fn { s with args := #[arg] ++ s.args, pos := s.pos.pushAppFn }
    return { s' with args := s.args, pos := s.pos }

  visitArg (arg : Expr) (s : State) : MetaM State := do
    let s' ← go arg { s with args := #[], pos := s.pos.pushAppArg }
    return { s' with args := s.args, pos := s.pos }

end TcProjs

section Reductions

/-
We do not generate reduction rewrites for *all* occurrences of type class projections, but instead
only for those which we deem relevant. Relevance is based on the appearance of symbols in the
reduction's target.

<TODO: Explain the selection strategy more specifically.>

In particular, the goal of these reduction rewrites in only to connect terms which both already
appear in other rewrites/guides/goals:

...<A>...                            ...<Z>...
    |      <A> => <B> ... <Y> => <Z>     |
    --------------------------------------

The goal is *not* to connect two different type class projections which happen to reduce to the same
term:

...<A>...                              ...<A'>...
    |                                      |
    -- <A> => <B> ... <Z> ... <B'> <= <A'>--

This latter approach wouldn't allow us to prune any type class projections, and we don't expect it
to be useful in practice.

To avoid the latter case being relevant, we need to make sure to generate *all* intermediate
reductions of a type class projection. As an example, consider `HAdd Nat Nat Nat` and `Add Nat`. If
we fully reduce their projections, they both reduce to `Nat.add`, thus proving them equal. However,
if `Nat.add` does not appear anywhere else, we do not generate these projections. We do not run into
this problem by considering two reductions for `HAdd`: `HAdd => Add` and `Add => Nat.add`. The
latter will be discarded (assuming `Nat.add` does not appear anywhere else), while the former will
be retained. Thus, the `HAdd` to `Add` equality is still provable.
-/

-- TODO: Consider the TODOs in "TC Proj Binders.lean" and "TC Diamonds.lean"
-- TODO: Fuze the reductions `HAdd => Add` and `Add => Nat.add` when `Add` doesn't appear.

private abbrev Reductions    := ExprMap Expr
private abbrev ReductionInfo := ExprMap Source

namespace Reductions

private def terminal (reds : Reductions) : List (Expr × Expr) :=
  reds.fold (init := []) fun acc src dst =>
    if reds.contains dst then acc else (src, dst) :: acc

private partial def active (reds : Reductions) (isActive : Expr → Bool) : List (Expr × Expr) := Id.run do
  let mut reds      := reds
  let mut active    := []
  let mut activated := (∅ : ExprSet)
  while !reds.isEmpty do
    for (src, dst) in reds.terminal do
      if dst ∈ activated || isActive dst then
        active    := (src, dst) :: active
        activated := activated.insert src
      reds := reds.erase src
  return active

private structure CollectionM.State where
  reds : Reductions
  info : ReductionInfo
  pre  : SourcePrefix

private abbrev CollectionM := StateT CollectionM.State MetaM

namespace CollectionM

private def setPrefix (pre : SourcePrefix) : CollectionM Unit :=
  modify fun s => { s with pre }

private def collect (src dst : Expr) (depth : Nat) : CollectionM Unit :=
  modify fun { reds, info, pre } => {
    reds := reds.insert src dst,
    info := info.insert src (.tcProj pre.src pre.loc pre.pos depth)
    pre
  }

private def run (m : CollectionM Unit) : MetaM (Reductions × ReductionInfo) := do
  let dummy := { src := .goal, loc := .root, pos := .root }
  let (_, state) ← m.run { reds := ∅, info := ∅, pre := dummy }
  return (state.reds, state.info)

end CollectionM

open CollectionM in
private partial def «from» (projs : TcProjs) (cfg : Config.Normalization) :
    MetaM (Reductions × ReductionInfo) := do
  CollectionM.run do
    for (proj, pre) in projs do
      setPrefix pre
      go proj (depth := 0)
where
  go (proj : Expr) (depth : Nat) : CollectionM Unit := do
    let some tgt ← unfoldProjInst? proj | return
    -- TODO: Reenable if necessary.
    -- Since we have type class instance erasure, we are not interested in type class projections
    -- which only transform a given type class instance into another type class instance.
    --
    -- if ← Meta.isTCInstance u then | return reds
    let tgt ← normalize tgt cfg
    collect proj tgt depth
    go tgt (depth + 1)

end Reductions

-- Note: This function expects its inputs' expressions to be normalized (cf. `Egg.normalize`).
def genTcProjReductions (targets : Array TcProjTarget) (cfg : Config.Normalization) :
    MetaM Rewrites := do
  -- TODO: Do we construct the `isActive` function during the traversal of `TcProjs.from`?
  let projs ← TcProjs.from targets
  let (reds, info) ← Reductions.from projs cfg
  let active := reds.active (isActive := fun _ => true)
  makeRewrites active info
where
  makeRewrites (reds : List <| Expr × Expr) (info : ReductionInfo) : MetaM Rewrites := do
    let mut rws := #[]
    for (lhs, rhs) in reds do
      let eq ← mkEq lhs rhs
      let proof ← mkEqRefl lhs
      let some src := info[lhs]?
        | throwError "egg: internal error in 'genTcProjReductions.makeRewrites'"
      let some rs ← Rewrites.from? proof eq src cfg (normalize := false)
        | throwError "egg: internal error in 'genTcProjReductions.makeRewrites'"
      rws := rws ++ rs
    return rws
