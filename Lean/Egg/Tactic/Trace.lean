import Egg.Core.Request
import Lean
open Lean Meta Elab Tactic Std Format

initialize registerTraceClass `egg
initialize registerTraceClass `egg.config (inherited := true)
initialize registerTraceClass `egg.rewrites (inherited := true)
initialize registerTraceClass `egg.encoded (inherited := true)
initialize registerTraceClass `egg.reconstruction (inherited := true)

namespace Egg

def Config.Debug.ExitPoint.format : Config.Debug.ExitPoint → Format
  | .none        => "None"
  | .beforeEqSat => "Before Equality Saturation"
  | .beforeProof => "Before Proof Reconstruction"

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

def Config.trace (cfg : Config) (cls : Name) : TacticM Unit := do
  let toEmoji (b : Bool) := if b then "✅" else "❌"
  withTraceNode cls (fun _ => return "Configuration") do
    Lean.trace cls fun _ => m!"{toEmoji cfg.genTcProjRws} Generate Type Class Projection Rewrites"
    Lean.trace cls fun _ => m!"{toEmoji cfg.genTcSpecRws} Generate Type Class Specialization Rewrites"
    Lean.trace cls fun _ => m!"{toEmoji cfg.genNatLitRws} Enable Definitional Natural Number Literal Rewrites"
    Lean.trace cls fun _ => m!"{toEmoji cfg.genBetaRw} Enable β-Reduction"
    Lean.trace cls fun _ => m!"{toEmoji cfg.genEtaRw} Enable η-Reduction"
    Lean.trace cls fun _ => m!"{toEmoji cfg.blockInvalidMatches} Block Invalid Matches"
    Lean.trace cls fun _ => m!"{toEmoji cfg.shiftCapturedBVars} Correct BVar Indices"
    Lean.trace cls fun _ => m!"{toEmoji cfg.optimizeExpl} Optimize Explanation Length"
    withTraceNode cls (fun _ => return "Encoding") (collapsed := false) do
      Lean.trace cls fun _ => m!"{toEmoji cfg.betaReduceRws} β-Reduce Rewrites"
      Lean.trace cls fun _ => m!"{toEmoji cfg.etaReduceRws} η-Reduces Rewrites"
      Lean.trace cls fun _ => m!"{toEmoji cfg.eraseProofs} Erase Proofs"
      Lean.trace cls fun _ => m!"{toEmoji cfg.eraseLambdaDomains} Erase λ's Domains"
      Lean.trace cls fun _ => m!"{toEmoji cfg.eraseForallDomains} Erase ∀'s Domains"
    withTraceNode cls (fun _ => return "Debug") (collapsed := false) do
      Lean.trace cls fun _ => m!"Exit Point: {cfg.exitPoint.format}"
      Lean.trace cls fun _ => m!"E-Graph Visualization Export Path: {cfg.vizPath.getD "None"}"
      Lean.trace cls fun _ => m!"{toEmoji cfg.traceSubstitutions} Trace Substitutions"
      Lean.trace cls fun _ => m!"{toEmoji cfg.traceBVarCorrection} Trace BVar Index Correction"

def Request.trace (req : Request) (cls : Name) : TacticM Unit := do
  withTraceNode cls (fun _ => return "Goal") do
    Lean.trace cls fun _ => m!"LHS: {req.lhs}"
    Lean.trace cls fun _ => m!"RHS: {req.rhs}"
  let rwsHeader := s!"{if req.rws.isEmpty then "No " else ""}Rewrites"
  withTraceNode `egg.frontend (fun _ => return rwsHeader) do
    for rw in req.rws do
      rw.trace cls
  withTraceNode cls (fun _ => return "Guides") do
    for guide in req.guides do
      Lean.trace cls fun _ => guide
