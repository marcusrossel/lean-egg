import Egg.Core.Rewrites
import Lean
open Lean Meta

namespace Egg

-- We expect the `args` to contain `numParams + 1` elements where the `numParams + 1`th argument is
-- the typeclass instance argument for `const`. Also, not arguments can contain loos bvars and the
-- final argument (the typeclass instance) can not be an mvar.
private structure TcProj where
  const : Name
  lvls  : List Level
  args  : Array Expr
  deriving BEq, Hashable

abbrev TcProjIndex := HashMap TcProj Source

private def TcProj.reductionRewrite (proj : TcProj) (src : Source) : MetaM Rewrite := do
  let app := mkAppN (.const proj.const proj.lvls) proj.args
  let reduced := (← reduceAll app).eta
  let eq ← mkEq app reduced
  let proof ← mkEqRefl app
  let some rw ← Rewrite.from? proof eq src false | throwError "egg: internal error in 'TcProj.reductionRewrite?'"
  return rw

private structure State where
  projs   : HashMap TcProj Source := ∅
  args    : Array Expr            := #[]
  pos     : SubExpr.Pos           := .root
  deriving Inhabited

private partial def tcProjs (e : Expr) (src : Source) (side : Side) (init : TcProjIndex) :
    MetaM TcProjIndex :=
  State.projs <$> go e { projs := init }
where
  -- Note: We don't change the position when entering an `mdata`.
  go : Expr → State → MetaM State
    | .const c lvls                   => visitConst c lvls
    | .app fn arg                     => (visitFn fn arg) >=> (visitArg arg)
    | .lam _ _ b _ | .forallE _ _ b _ => visitBindingBody b
    | .mdata _ b                      => go b
    | .proj ..                        => panic! "egg: encountered `proj` in `Expr` expected not to contain it"
    | .letE ..                        => panic! "egg: encountered `letE` in `Expr` expected not to contain it"
    | _                               => pure

  visitConst (const : Name) (lvls : List Level) (s : State) : MetaM State := do
    let some info ← getProjectionFnInfo? const | return s
    unless info.fromClass && s.args.size > info.numParams do return s
    let args := s.args[:info.numParams + 1].toArray
    if args.back.isMVar || args.any (·.hasLooseBVars) then return s
    let projs := s.projs.insertIfNew { const, lvls, args } (.tcProj src side s.pos)
    return { s with projs }

  visitBindingBody (b : Expr) (s : State) : MetaM State := do
    let s' ← go b { s with pos := s.pos.pushBindingBody }
    return { s' with pos := s.pos }

  visitFn (fn : Expr) (arg : Expr) (s : State) : MetaM State := do
    let s' ← go fn { s with args := #[arg] ++ s.args, pos := s.pos.pushAppFn }
    return { s' with args := s.args, pos := s.pos }

  visitArg (arg : Expr) (s : State) : MetaM State := do
    let s' ← go arg { s with args := #[], pos := s.pos.pushAppArg }
    return { s' with args := s.args, pos := s.pos }

def Rewrites.tcProjReductions (rws : Rewrites) : MetaM Rewrites := do
  let mut projs : TcProjIndex := ∅
  for rw in rws do
    projs ← tcProjs rw.lhs rw.src .left  projs
    projs ← tcProjs rw.rhs rw.src .right projs
  projs.toArray.mapM fun (proj, src) => proj.reductionRewrite src
