import Egg.Core.Premise.Rewrites
import Egg.Core.Guides
import Lean
open Lean hiding HashMap HashSet
open Meta
open Std (HashMap HashSet)

namespace Egg

abbrev TcProj := Expr

private def TcProj.mk (const : Name) (args : Array Expr) (lvls : List Level) : TcProj :=
  mkAppN (.const const lvls) args

private structure TcProj.SrcPrefix where
  src : Source
  loc : Source.TcProjLocation
  pos : SubExpr.Pos

-- Note: This function expects `proj` to be normalized (cf. `Egg.normalize`).
private def TcProj.reductionRewrites
    (proj : TcProj) (src : TcProj.SrcPrefix) (cfg : Config.Normalization) :
    MetaM (Array Rewrite) := do
  let mut rws := #[]
  let mut proj := proj
  while true do
    if let some u ← unfoldProjInst? proj then
      -- Since we have type class instance erasure, we are not interested in type class projections
      -- which only transform a given type class instance into another type class instance.
      if ← Meta.isTCInstance u then break
      let uNorm ← normalize u cfg
      let eq ← mkEq proj uNorm
      let proof ← mkEqRefl proj
      let some rw ← Rewrite.from? proof eq (.tcProj src.src src.loc src.pos rws.size) cfg (normalize := false)
        | throwError "egg: internal error in 'TcProj.reductionRewrite?'"
      -- TODO: This is a bandaid. How do we handle unboundedd mvars in the types of tc instance
      --       conditions in general?
      let rw := rw.eraseConditions
      rws := rws.push rw
      -- TODO: If normalization for rewrites is turned off, this entails that we might generate
      --       fewer type class projection rewrites 😬
      proj := uNorm
    else
      break
  return rws

private abbrev TcProjIndex := HashMap TcProj TcProj.SrcPrefix

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
    | .lam _ d b _ | .forallE _ d b _ => (visitBindingDomain d) >=> (visitBindingBody b)
    | .mdata .. | .proj .. | .letE .. => fun _ => throwError "egg: internal error: 'Egg.tcProjs.go' received non-normalized expression"
    | _                               => pure

  visitConst (const : Name) (lvls : List Level) (s : State) : MetaM State := do
    let some info ← getProjectionFnInfo? const | return s
    unless info.fromClass && s.args.size > info.numParams do return s
    let args := s.args[:info.numParams + 1].toArray
    if args.back!.isMVar || args.any (·.hasLooseBVars) then return s
    let proj := TcProj.mk const args lvls
    if s.covers proj
    then return s
    else return { s with projs := s.projs.insert proj { src, loc, pos := s.pos } }

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

structure TcProjTarget where
  expr : Expr
  src  : Source
  loc  : Source.TcProjLocation

def Congr.tcProjTargets (cgr : Congr) (src : Source) : Array TcProjTarget := #[
  { expr := cgr.lhs, src := src, loc := .left },
  { expr := cgr.rhs, src := src, loc := .right }
]

def Rewrites.tcProjTargets (rws : Rewrites) : Array TcProjTarget := Id.run do
  let mut sources : Array TcProjTarget := #[]
  for rw in rws do
    sources := sources ++ rw.toCongr.tcProjTargets rw.src
    for cond in rw.conds, idx in [:rw.conds.size] do
      sources := sources.push { expr := cond.type, src := rw.src, loc := .cond idx }
  return sources

def Guides.tcProjTargets (guides : Guides) : Array TcProjTarget :=
  guides.map fun guide => { expr := guide.expr, src := guide.src, loc := .root }
--
-- Note: This function expects its inputs' expressions to be normalized (cf. `Egg.normalize`).
def genTcProjReductions
    (targets : Array TcProjTarget) (covered : HashSet TcProj) (cfg : Config.Normalization) :
    MetaM (Rewrites × HashSet TcProj) := do
  let mut covered := covered
  let mut rws := #[]
  for target in targets do
    let projs ← tcProjs target.expr target.src target.loc covered
    for (proj, src) in projs.toArray do
      covered := covered.insert proj
      rws := rws ++ (← proj.reductionRewrites src cfg)
  return (rws, covered)
