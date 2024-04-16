import Egg.Core.Request
import Lean
open Lean Meta Elab Tactic Std Format

initialize registerTraceClass `egg
initialize registerTraceClass `egg.rewrites (inherited := true)
initialize registerTraceClass `egg.frontend (inherited := true)
initialize registerTraceClass `egg.reconstruction (inherited := true)

namespace Egg

nonrec def MVars.format (mvars : MVars) : MetaM Format := do
  let expr := format <| ← mvars.expr.toList.mapM (ppExpr <| Expr.mvar ·)
  let tc   := format <| ← mvars.tc.toList.mapM   (ppExpr <| Expr.mvar ·)
  let lvl  := format <|   mvars.lvl.toList.map   (Level.mvar ·)
  return "expr: " ++ expr ++ "\n" ++ "class: " ++ tc ++ "\n" ++ "level: " ++ lvl

def Directions.format : Directions → Format
  | .none     => "∅"
  | .forward  => "⇒"
  | .backward => "⇐"
  | .both     => "⇔"

def Congr.Rel.format : Congr.Rel → Format
  | .eq  => "="
  | .iff => "↔"

def Congr.format (cgr : Congr) : MetaM Format :=
  return (← ppExpr cgr.lhs) ++ " " ++ cgr.rel.format ++ " " ++ (← ppExpr cgr.rhs)

def Rewrite.trace (rw : Rewrite) (stx? : Option Syntax) (cls : Name) : TacticM Unit := do
  let mut header := m!"{rw.src.description}({rw.validDirs.format})"
  if let some stx := stx? then header := m!"{header}: {stx}"
  withTraceNode cls (fun _ => return header) do
    Lean.traceM cls fun _ => return m!"{← rw.toCongr.format}"
    Lean.traceM cls fun _ => return m!"LHS MVars\n{← rw.lhsMVars.format}"
    Lean.traceM cls fun _ => return m!"RHS MVars\n{← rw.rhsMVars.format}"

def Rewrites.trace (rws : Rewrites) (stx : Array Syntax) (cls : Name) : TacticM Unit := do
  for rw in rws, idx in [:rws.size] do rw.trace stx[idx]? cls

def Rewrite.Encoded.trace (rw : Rewrite.Encoded) (cls : Name) : TacticM Unit := do
  let header := m!"{rw.name}({rw.dirs.format})"
  withTraceNode cls (fun _ => return header) do
    Lean.trace cls fun _ => m!"LHS: {rw.lhs}"
    Lean.trace cls fun _ => m!"RHS: {rw.rhs}"

def Request.trace (req : Request) : TacticM Unit := do
  withTraceNode `egg.frontend (fun _ => return "Request") do
    withTraceNode `egg.frontend (fun _ => return "Goal") (collapsed := false) do
      withTraceNode `egg.frontend (fun _ => return "LHS") do trace[egg.frontend] req.lhs
      withTraceNode `egg.frontend (fun _ => return "RHS") do trace[egg.frontend] req.rhs
    let rwsTitle := (if req.rws.isEmpty && !req.cfg.genNatLitRws then "No " else "") ++ "Rewrites"
    withTraceNode `egg.frontend (fun _ => return rwsTitle) (collapsed := false) do
      for rw in req.rws do rw.trace `egg.frontend
      if req.cfg.genNatLitRws then trace[egg.frontend] "Nat Literal Conversions"
