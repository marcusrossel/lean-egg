import Egg.Core.Premise.Rewrites
import Egg.Core.Guides
import Lean
open Lean hiding HashMap HashSet
open Meta
open Std (HashMap HashSet)

namespace Egg

abbrev TcProj := Expr

private def TcProj.ofConst (const : Name) (args : Array Expr) (lvls : List Level) : TcProj :=
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
    let some unfolded ← if proj.isProj then reduceProj? proj else unfoldProjInst? proj | break
    -- Since we have type class instance erasure, we are not interested in type class projections
    -- which only transform a given type class instance into another type class instance.
    if ← Meta.isTCInstance unfolded then break
    let uNorm ← normalize unfolded cfg
    let eq ← mkEq proj uNorm
    let proof ← mkEqRefl proj
    let some rw ← Rewrite.from? proof eq (.tcProj src.src src.loc src.pos rws.size) cfg (normalize := false)
      | throwError "egg: internal error in 'TcProj.reductionRewrites'"
    -- TODO: This is a bandaid. How do we handle unbounded mvars in the types of tc instance
    --       conditions in general?
    let rw := rw.eraseConditions
    rws    := rws.push rw
    proj   := uNorm
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
    | .proj ty idx b                   => visitProj ty idx b
    | .mdata .. | .letE ..            => fun _ => throwError "egg: internal error: 'Egg.tcProjs.go' received non-normalized expression"
    | _                               => pure

  visitProj (structName : Name) (idx : Nat) (body : Expr) (s : State) : MetaM State := do
    unless isClass (← getEnv) structName do return s
    let proj := .proj structName idx body
    let projs :=
      if s.covers proj
      then s.projs
      else s.projs.insert (.proj structName idx body) { src, loc, pos := s.pos }
    go body { s with projs, args := #[], pos := s.pos.pushProj }

  -- TODO: This doesn't seem quite right. For example, why are we checking whether the number of
  --       args is > numParams?
  visitConst (const : Name) (lvls : List Level) (s : State) : MetaM State := do
    let some info ← getProjectionFnInfo? const | return s
    unless info.fromClass && s.args.size > info.numParams do return s
    let args := s.args[:info.numParams + 1].toArray
    if args.back!.isMVar || args.any (·.hasLooseBVars) then return s
    let proj := TcProj.ofConst const args lvls
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
