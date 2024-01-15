import Lean
import Std.Lean.HashSet

namespace Lean

-- Note: The `_uniq` prefix comes from the `MonadNameGenerator`.

def Expr.getFVars (e : Expr) : Array FVarId :=
  Lean.collectFVars {} e |>.fvarIds

def FVarId.uniqueIdx! : FVarId → Nat
  | { name := .num (.str .anonymous "_uniq") idx } => idx
  | _ => panic! "tried to access unique index of non-unique fvar-id"

def MVarId.uniqueIdx! : MVarId → Nat
  | { name := .num (.str .anonymous "_uniq") idx } => idx
  | _ => panic! "tried to access unique index of non-unique mvar-id"

def LMVarId.uniqueIdx! : LMVarId → Nat
  | { name := .num (.str .anonymous "_uniq") idx } => idx
  | _ => panic! "tried to access unique index of non-unique level mvar-id"

def Level.levelMVars : Level → HashSet LMVarId
    | mvar id                => {id}
    | zero | param _         => ∅
    | succ l                 => l.levelMVars
    | max l₁ l₂ | imax l₁ l₂ => l₁.levelMVars.merge l₂.levelMVars

def Expr.levelMVars : Expr → HashSet LMVarId
  | sort lvl => lvl.levelMVars
  | const _ lvls => lvls.foldl (·.merge ·.levelMVars) ∅
  | bvar _ | fvar _ | mvar _ | lit _ => ∅
  | mdata _ e | proj _ _ e => e.levelMVars
  | app e₁ e₂ | lam _ e₁ e₂ _ | forallE _ e₁ e₂ _ => e₁.levelMVars.merge e₂.levelMVars
  | letE _ e₁ e₂ e₃ _ => e₁.levelMVars.merge e₂.levelMVars |>.merge e₃.levelMVars

protected def throwErrorAt? [Monad m] [MonadError m] (ref? : Option Syntax) (msg : MessageData) : m α := do
  if let some ref := ref?
  then Lean.throwErrorAt ref msg
  else Lean.throwError msg

syntax "throwErrorAt? " term:max ppSpace (interpolatedStr(term) <|> term) : term

macro_rules
  | `(throwErrorAt? $ref $msg:interpolatedStr) => `(Lean.throwErrorAt? $ref (m! $msg))
  | `(throwErrorAt? $ref $msg:term)            => `(Lean.throwErrorAt? $ref $msg)
