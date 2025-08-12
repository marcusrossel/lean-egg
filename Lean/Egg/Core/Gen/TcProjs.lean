import Egg.Core.Rewrite.Rule
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

def Rewrite.Rules.tcProjTargets (rules : Rewrite.Rules) : Array TcProjTarget := Id.run do
  let mut sources : Array TcProjTarget := #[]
  for rule in rules.entries do
    sources := sources ++ rule.rw.tcProjTargets rule.src
    for cond in rule.rw.conds.active, idx in [:rule.rw.conds.active.size] do
      sources := sources.push { expr := cond.type, src := rule.src, loc := .cond idx }
  return sources

def Guides.tcProjTargets (guides : Guides) : Array TcProjTarget :=
  guides.map fun guide => { expr := guide.expr, src := guide.src, loc := .root }

private structure SourcePrefix where
  src : Source
  loc : Source.TcProjLocation
  pos : SubExpr.Pos

section TcProjs

private abbrev TcProjs := ExprMap SourcePrefix

private inductive Symbol where
  | const (n : Name)
  | natLit
deriving BEq, Hashable

private abbrev Symbols := HashSet Symbol

private structure State where
  projs   : TcProjs     := ∅
  args    : Array Expr  := #[]
  pos     : SubExpr.Pos := .root
  src     : Source
  loc     : Source.TcProjLocation
  symbols : Symbols := ∅

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

private partial def TcProjs.from (targets : Array TcProjTarget) : MetaM (TcProjs × Symbols) := do
  -- Note: These initial values are dummy values which are properly set before first use.
  let mut state := { src := .goal, loc := .root }
  for { expr, src, loc } in targets do
    state ← go expr { state with src, loc }
  return (state.projs, state.symbols)
where
  go : Expr → State → MetaM State
    | .const c lvls                   => visitConst c lvls
    | .app fn arg                     => (visitFn fn arg) >=> (visitArg arg)
    | .lam _ d b _ | .forallE _ d b _ => (visitBindingDomain d) >=> (visitBindingBody b)
    | .mdata .. | .proj .. | .letE .. => fun _ => throwError "egg: internal error: 'Egg.tcProjs.go' received non-normalized expression"
    | .lit (.natVal _)                => visitNatLit
    | _                               => pure

  visitConst (const : Name) (lvls : List Level) (s : State) : MetaM State := do
    -- Record the symbol name, if it is not a type class instance.
    let s := if ← isInstance const then s else { s with symbols := s.symbols.insert (.const const) }
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

  visitNatLit (s : State) : MetaM State := do
    return { s with symbols := s.symbols.insert .natLit }

end TcProjs

/-
We do not generate reduction rewrites for *all* occurrences of type class projections, but instead
only for those which we deem relevant. Relevance is based on the appearance of symbols in the
reduction's target.
Specifically, we expect all involved expressions to have a head-symbol (i.e. they need to be of the
form `f`, `f a`, `f a b`, ...). If the head symbol does not appear in any other rewrite, guide, or
the proof goal, then we deem the rewrite irrelevant. Also, we exclude type class instance from the
set of relevant symbols, as they are erased during encoding.

As a practical matter, the goal of these reduction rewrites in only to connect terms which both
already appear in other rewrites/guides/goals:

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

private abbrev Reductions    := ExprMap Expr
private abbrev ReductionInfo := ExprMap Source

namespace Reductions

private def «from» (projs : TcProjs) (cfg : Config.Normalization) : MetaM (Reductions × ReductionInfo) := do
  let mut reds : Reductions    := ∅
  let mut info : ReductionInfo := ∅
  for (proj, pre) in projs do
    let mut proj := proj
    let mut depth := 0
    repeat
      let some tgt ← unfoldProjInst? proj | break
      -- TODO: Reenable if necessary.
      -- Since we have type class instance erasure, we are not interested in type class projections
      -- which only transform a given type class instance into another type class instance.
      -- `if ← Meta.isTCInstance u then | return reds`
      let tgt ← normalize tgt cfg
      reds := reds.insert proj tgt
      info := info.insert proj (.tcProj pre.src pre.loc pre.pos depth)
      depth := depth + 1
      proj := tgt
  return (reds, info)

private def terminal (reds : Reductions) : List (Expr × Expr) :=
  reds.fold (init := []) fun acc src dst =>
    if reds.contains dst then acc else (src, dst) :: acc

private inductive ActivationReason where
  | external
  | internal
deriving Inhabited

instance : ToString ActivationReason where
  toString
    | .external => "external"
    | .internal => "internal"

private def ActivationReason.join : ActivationReason → ActivationReason → ActivationReason
  | internal, internal => internal
  | _, _               => external

private structure Activations where
  reductions : Reductions
  reasons    : ExprMap ActivationReason

private def Activations.ofExternal (es : List Expr) : Activations where
  reductions := ∅
  reasons := es.foldl (init := ∅) (·.insert · .external)

private def Activations.insert (acts : Activations) (src dst : Expr) (external : Bool) : Activations :=
  let reductions := acts.reductions.insert src dst
  -- If a reduction was activated both externally and internally, we want to mark it as being
  -- activated externally, as this is stronger (internal might lead to fuzing, external not).
  let reason : ActivationReason := if external then .external else .internal
  -- If the `src` has already been activated, we make sure to retain the stronger reason.
  let reasons := acts.reasons.alter dst fun
    | none     => reason
    | some rsn => rsn.join reason
  { reductions, reasons }

-- We determine activation of reductions starting from terminal reductions. A terminal reduction is
-- activated if its destination is. After deciding activation for all terminal reduction, we remove
-- all terminal reductions from the set of candidates and repeat the process. This way, we
-- iteratively "peel off" the terminal reductions from the (dependency) graph of reductions, until
-- none are left.
private def activations (reds : Reductions) (initial : List Expr) (symbols : Symbols) :
    MetaM Activations := do
  -- We set the activation reasons of the `initial` expressions (i.e. those expressions which were
  -- found by `TcProjs.from`) to `external`, as the subsequent procedure does not necessarily set
  -- their reason otherwise.
  let mut acts      := .ofExternal initial
  let mut activated := (∅ : ExprSet)
  let mut reds      := reds
  while !reds.isEmpty do
    for (src, dst) in reds.terminal do
      -- A destination is considered active, either if it appears in any of the "external" rewrites,
      -- guides, or the proof goal (via `isActive`), *or* if we have already activated another
      -- reduction which has the destination as its source. As a result, parents of activated
      -- reductions also become activated (which we want). For example, If `Add => Nat.add` is
      -- activated, then `Add` is added to `activated`, an in turn (in the next iteration of the
      -- `while`-loop), `HAdd => Add` will be activated.
      let some external ← isActive dst
        | throwError m!"egg: internal error in 'Reductions.activations'. Received:\n\n  {src}\n\n⇒\n\n  {dst}"
      let internal := dst ∈ activated
      if external || internal then
        acts := acts.insert src dst external
        activated := activated.insert src
      reds := reds.erase src
  return acts
where
  isActive (e : Expr) : MetaM (Option Bool) := do
    lambdaTelescope e fun _ e =>
      if let .const n _ := e.getAppFn then
        return symbols.contains (.const n)
      else if let .lit (.natVal _) := e then
        return symbols.contains .natLit
      else
        return none

-- Fuzes reductions which are only linked by terms with `ActivationReason.internal`.
private def Activations.fuze (acts : Activations) : MetaM <| List (Expr × Expr) := do
  let mut { reductions := reds, reasons } := acts
  let mut todos := reds.keys
  repeat
    -- Note: We never remove anything from `reds`. For example, for a reduction `e₁ ⇒ e₂ ⇒ e₃` where
    --       `e₂` is internal, we simply update `e₁` to `e₁ ⇒ e₃`, while retaining `e₂ ⇒ e₃`.
    let e₁ :: todos' := todos | break
    todos := todos'
    let e₂ := reds[e₁]!
    -- If the reduction is terminal (note: terminal reductions can never be internal), we don't need
    -- to do anything and `continue`.
    let some e₃ := reds[e₂]? | continue
    -- If the middle element `e₂` of the reduction chain `e₁ ⇒ e₂ ⇒ e₃` is not internal (i.e. it is
    -- external), the the reduction chain should remain unchanged and we `continue`.
    let .internal := reasons[e₂]! | continue
    -- If the element `e₂` is internal, contract the reduction from `e₁` to go directly to `e₃`.
    reds := reds.insert e₁ e₃
    -- Add `e₁` back to the queue, as it might admit more contractions.
    todos := e₁ :: todos
  -- At this point all reductions from `external` elements point only to other `external` elements,
  -- and all reductions starting at `internal` elements are redundant.
  let mut result := []
  for (src, dst) in reds do
    if let .external := reasons[src]! then result := (src, dst) :: result
  return result

end Reductions

-- Note: This function expects its inputs' expressions to be normalized (cf. `Egg.normalize`).
def genTcProjReductions (targets : Array TcProjTarget) (cfg : Config) : MetaM Rewrite.Rules := do
  let (projs, symbols) ← TcProjs.from targets
  let (reds, info) ← Reductions.from projs cfg
  let acts ← reds.activations projs.keys (symbols ∪ backendSymbols)
  if cfg.tcProjFusion then
    let fuzed ← acts.fuze
    makeRewrites fuzed info
  else
    makeRewrites acts.reductions.toList info
where
  makeRewrites (reds : List <| Expr × Expr) (info : ReductionInfo) : MetaM Rewrite.Rules := do
    let mut rules := ∅
    for (lhs, rhs) in reds do
      let eq ← mkEq lhs rhs
      let proof ← mkEqRefl lhs
      let some src := info[lhs]?
        | throwError "egg: internal error in 'genTcProjReductions.makeRewrites'"
      let some rules' ← rules.add? src proof eq cfg (normalize := false)
        | throwError "egg: internal error in 'genTcProjReductions.makeRewrites'"
      rules := rules'
    return rules
  backendSymbols : Symbols := Id.run do
    let mut symbols := { .const ``True, .const ``And }
    if cfg.natLit then
      symbols := symbols ∪ {
        .natLit, .const ``Nat.zero, .const ``Nat.add, .const ``Nat.sub, .const ``Nat.mul,
        .const ``Nat.pow, .const ``Nat.div, .const ``Nat.mod
      }
    return symbols
