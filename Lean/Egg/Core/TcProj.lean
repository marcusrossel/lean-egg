import Egg.Core.Rewrites
import Lean
open Lean Meta

namespace Egg

-- We expect the `args` to contain `numParams + 1` elements where the `numParams + 1`th argument is
-- the type class instance argument for `const`.
structure TcProj where
  const : Name
  lvls  : List Level
  args  : Array Expr
  deriving BEq, Hashable

def TcProj.reductionRewrite? (proj : TcProj) (src : Source) : MetaM (Option Rewrite) := do
  let some tcArg := proj.args.back? | return none
  unless !tcArg.isMVar do return none
  let app := mkAppN (.const proj.const proj.lvls) proj.args
  let reduced := (← reduceAll app).eta
  let eq ← mkEq app reduced
  let proof ← mkEqRefl app
  let some rw ← Rewrite.from? proof eq src false
    | throwError "egg: internal error in 'TcProj.reductionRewrite?'"
  return rw
