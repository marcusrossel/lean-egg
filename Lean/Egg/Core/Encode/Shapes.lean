import Lean
open Lean

namespace Egg

abbrev Shape := String

partial def shape : Expr → Shape
  | .fvar _ | .mvar _ | .sort _ | .const .. | .app .. | .lit _ | .bvar _ | .proj .. => "\"*\""
  | .lam _ ty b _ | .forallE _ ty b _ => s!"(→ {shape ty} {shape b})"
  | .mdata _ e => shape e
  | .letE .. => panic! "'Egg.shape' received let-expression"

open Meta Elab Term Command

scoped elab "#shape" t:term : command => liftTermElabM do
  logInfo <| shape <| ← inferType <| ← elabTerm t none

scoped elab "show_shape" t:term : tactic => do
  logInfo <| shape <| ← inferType <| ← elabTerm t none
