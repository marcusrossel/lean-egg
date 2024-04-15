import Egg.Core.Rewrites
import Egg.Core.Guides
import Lean
open Lean Meta

namespace Egg

-- We expect the `args` to contain `numParams + 1` elements where the `numParams + 1`th argument is
-- the typeclass instance argument for `const`. Also, not arguments can contain loos bvars and the
-- final argument (the typeclass instance) can not be an mvar.
structure TcProj where
  const : Name
  lvls  : List Level
  args  : Array Expr
  deriving BEq, Hashable

abbrev TcProjIndex := HashMap TcProj Source

private def TcProj.reductionRewrite? (proj : TcProj) (src : Source) (beta eta : Bool) :
    MetaM (Option Rewrite) := do
  let app := mkAppN (.const proj.const proj.lvls) proj.args
  let reduced ← withReducibleAndInstances do reduceAll app
  if app == reduced then return none
  let eq ← mkEq app reduced
  let proof ← mkEqRefl app
  let some rw ← Rewrite.from? proof eq src beta eta | throwError "egg: internal error in 'TcProj.reductionRewrite'"
  return rw

private structure State where
  projs   : TcProjIndex    := ∅
  args    : Array Expr     := #[]
  pos     : SubExpr.Pos    := .root
  covered : HashSet TcProj := ∅
  deriving Inhabited

private partial def tcProjs
    (e : Expr) (src : Source) (side? : Option Side) (covered : HashSet TcProj) :
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
    let proj : TcProj := { const, lvls, args }
    return { s with
      projs :=
        if s.covered.contains proj
        then s.projs
        else s.projs.insertIfNew proj (.tcProj src side? s.pos)
    }

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
  expr  : Expr
  src   : Source
  side? : Option Side

def Rewrites.tcProjTargets (rws : Rewrites) : Array TcProjTarget := Id.run do
  let mut sources : Array TcProjTarget := #[]
  for rw in rws do
    sources := sources.push { expr := rw.lhs, src := rw.src, side? := some .left }
    sources := sources.push { expr := rw.rhs, src := rw.src, side? := some .right }
  return sources

def Guides.tcProjTargets (guides : Guides) : Array TcProjTarget :=
  guides.map fun guide => { expr := guide.expr, src := guide.src, side? := none }

-- Note: This function expects its inputs' expressions to be normalized (cf. `Egg.normalize`).
def genTcProjReductions'
    (targets : Array TcProjTarget) (covered : HashSet TcProj) (beta eta : Bool) :
    MetaM (Rewrites × HashSet TcProj) := do
  let mut covered := covered
  let mut rws := #[]
  for target in targets do
    let projs ← tcProjs target.expr target.src target.side? covered
    for (proj, src) in projs.toArray do
      covered := covered.insert proj
      if let some rw ← proj.reductionRewrite? src beta eta then rws := rws.push rw
  return (rws, covered)

def genTcProjReductions (targets : Array TcProjTarget) (beta eta : Bool) : MetaM Rewrites :=
  Prod.fst <$> genTcProjReductions' targets ∅ beta eta
