import Egg.Core.Premise.Basic
import Egg.Core.Guides
import Lean
open Lean Meta

namespace Egg

abbrev TcProj := Expr

private def TcProj.mk (const : Name) (args : Array Expr) (lvls : List Level) : TcProj :=
  mkAppN (.const const lvls) args

-- Note: This function expects `proj` to be normalized (cf. `Egg.normalize`).
private def TcProj.reductionRewrite?
    (proj : TcProj) (src : Source) (norm : Config.Normalization) (amb : MVars.Ambient) :
    MetaM (Option Rewrite) := do
  -- Sometimes the only reduction performed by `reduceAll` is to replace a application of a type
  -- class projection with its corresponding `Expr.proj` expression. In that case, no real reduction
  -- has been performed for our purposes. To catch these cases, we normalize `reduced` (which
  -- expands `Expr.proj`s) *before* checking for equality with `proj`, and in return *don't*
  -- normalize again in `Rewrite.from?`.
  let reduced ← withReducibleAndInstances do reduceAll proj
  let reducedNorm ← normalize reduced norm
  if proj == reducedNorm then return none
  let eq ← mkEq proj reducedNorm
  let proof ← mkEqRefl proj
  let .rw rw ← Premise.from proof eq src none amb
    | throwError "egg: internal error in 'TcProj.reductionRewrite?'"
  return rw

abbrev TcProjIndex := HashMap TcProj Source

private structure State where
  projs   : TcProjIndex    := ∅
  args    : Array Expr     := #[]
  pos     : SubExpr.Pos    := .root
  covered : HashSet TcProj := ∅
  deriving Inhabited

private def State.covers (s : State) (proj : TcProj) : Bool :=
  s.covered.contains proj || s.projs.contains proj

private partial def tcProjs
    (e : Expr) (src : Source) (loc : Source.TcProjLocation) (covered : HashSet TcProj) :
    MetaM TcProjIndex :=
  State.projs <$> go e { covered }
where
  go : Expr → State → MetaM State
    | .const c lvls                   => visitConst c lvls
    | .app fn arg                     => (visitFn fn arg) >=> (visitArg arg)
    | .lam _ _ b _ | .forallE _ _ b _ => visitBindingBody b
    | .mdata .. | .proj .. | .letE .. => panic! "'Egg.tcProjs.go' received non-normalized expression"
    | _                               => pure

  visitConst (const : Name) (lvls : List Level) (s : State) : MetaM State := do
    let some info ← getProjectionFnInfo? const | return s
    unless info.fromClass && s.args.size > info.numParams do return s
    let args := s.args[:info.numParams + 1].toArray
    if args.back.isMVar || args.any (·.hasLooseBVars) then return s
    let proj := TcProj.mk const args lvls
    if s.covers proj
    then return s
    else return { s with projs := s.projs.insert proj (.tcProj src loc s.pos) }

  visitBindingBody (b : Expr) (s : State) : MetaM State := do
    let s' ← go b { s with pos := s.pos.pushBindingBody }
    return { s' with pos := s.pos }

  visitFn (fn : Expr) (arg : Expr) (s : State) : MetaM State := do
    let s' ← go fn { s with args := #[arg] ++ s.args, pos := s.pos.pushAppFn }
    return { s' with args := s.args, pos := s.pos }

  visitArg (arg : Expr) (s : State) : MetaM State := do
    let s' ← go arg { s with args := #[], pos := s.pos.pushAppArg }
    return { s' with args := s.args, pos := s.pos }

structure TcProjTarget where
  expr : Expr
  src  : Source
  loc  : Source.TcProjLocation

def Rewrites.tcProjTargets (rws : Rewrites) : Array TcProjTarget := Id.run do
  let mut sources : Array TcProjTarget := #[]
  for rw in rws do
    sources := sources.push { expr := rw.lhs, src := rw.src, loc := .left }
    sources := sources.push { expr := rw.rhs, src := rw.src, loc := .right }
    for cond in rw.conds, idx in [:rw.conds.size] do
      sources := sources.push { expr := cond, src := rw.src, loc := .cond idx }
  return sources

def Facts.tcProjTargets (facts : Facts) : Array TcProjTarget :=
  facts.map fun fact => { expr := fact.type, src := fact.src, loc := .root }

def Guides.tcProjTargets (guides : Guides) : Array TcProjTarget :=
  guides.map fun guide => { expr := guide.expr, src := guide.src, loc := .root }

-- TODO: This still produces many redundant rewrites which differ only by mvars. Is there an
--       efficient way to check if two `TcProj`s are equal up to mvar renaming?
--       Note that for this check to be valid, you also need to know which mvars are "local" and
--       which are ambient.
--
-- Note: This function expects its inputs' expressions to be normalized (cf. `Egg.normalize`).
def genTcProjReductions
    (targets : Array TcProjTarget) (covered : HashSet TcProj) (norm : Config.Normalization)
    (amb : MVars.Ambient) : MetaM (Rewrites × HashSet TcProj) := do
  let mut covered := covered
  let mut rws := #[]
  for target in targets do
    let projs ← tcProjs target.expr target.src target.loc covered
    for (proj, src) in projs.toArray do
      covered := covered.insert proj
      if let some rw ← proj.reductionRewrite? src norm amb then rws := rws.push rw
  return (rws, covered)
