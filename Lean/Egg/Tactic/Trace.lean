import Egg.Core.Request
import Egg.Core.Explanation.Proof
import Egg.Core.MVars.Ambient
import Lean
open Lean Meta Elab Tactic Std Format

initialize registerTraceClass `egg
initialize registerTraceClass `egg.config      (inherited := true)
initialize registerTraceClass `egg.rewrites    (inherited := true)
initialize registerTraceClass `egg.ambient     (inherited := true)
initialize registerTraceClass `egg.encoded     (inherited := true)
initialize registerTraceClass `egg.explanation (inherited := true)
initialize registerTraceClass `egg.proof       (inherited := true)
initialize registerTraceClass `egg.proof.term  (inherited := false)

namespace Egg

def Config.Debug.ExitPoint.format : Config.Debug.ExitPoint → Format
  | .none        => "None"
  | .beforeEqSat => "Before Equality Saturation"
  | .beforeProof => "Before Proof Reconstruction"

nonrec def MVars.format (mvars : MVars) : MetaM Format := do
  let expr := format <| ← mvars.expr.toList.mapM (ppExpr <| Expr.mvar ·)
  let tc   := format <| ← mvars.tc.toList.mapM   (ppExpr <| Expr.mvar ·)
  let lvl  := format <|   mvars.lvl.toList.map   (Level.mvar ·)
  return "expr:  " ++ expr ++ "\n" ++ "class: " ++ tc ++ "\n" ++ "level: " ++ lvl

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
    traceM cls fun _ => return m!"{← rw.toCongr.format}"
    traceM cls fun _ => return m!"LHS MVars\n{← rw.lhsMVars.format}"
    traceM cls fun _ => return m!"RHS MVars\n{← rw.rhsMVars.format}"

def Rewrites.trace (rws : Rewrites) (stx : Array Syntax) (cls : Name) : TacticM Unit := do
  for rw in rws, idx in [:rws.size] do rw.trace stx[idx]? cls

def Rewrite.Encoded.trace (rw : Rewrite.Encoded) (cls : Name) : TacticM Unit := do
  let header := m!"{rw.name}({rw.dirs.format})"
  withTraceNode cls (fun _ => return header) do
    Lean.trace cls fun _ => m!"LHS: {rw.lhs}"
    Lean.trace cls fun _ => m!"RHS: {rw.rhs}"

nonrec def Config.trace (cfg : Config) (cls : Name) : TacticM Unit := do
  let toEmoji (b : Bool) := if b then "✅" else "❌"
  withTraceNode cls (fun _ => return "Configuration") do
    trace cls fun _ => m!"{toEmoji cfg.genTcProjRws} Generate Type Class Projection Rewrites"
    trace cls fun _ => m!"{toEmoji cfg.genTcSpecRws} Generate Type Class Specialization Rewrites"
    trace cls fun _ => m!"{toEmoji cfg.genNatLitRws} Enable Definitional Natural Number Literal Rewrites"
    trace cls fun _ => m!"{toEmoji cfg.genBetaRw} Enable β-Reduction"
    trace cls fun _ => m!"{toEmoji cfg.genEtaRw} Enable η-Reduction"
    trace cls fun _ => m!"{toEmoji cfg.blockInvalidMatches} Block Invalid Matches"
    trace cls fun _ => m!"{toEmoji cfg.shiftCapturedBVars} Correct BVar Indices"
    trace cls fun _ => m!"{toEmoji cfg.optimizeExpl} Optimize Explanation Length"
    withTraceNode cls (fun _ => return "Encoding") (collapsed := false) do
      trace cls fun _ => m!"{toEmoji cfg.betaReduceRws} β-Reduce Rewrites"
      trace cls fun _ => m!"{toEmoji cfg.etaReduceRws} η-Reduces Rewrites"
      trace cls fun _ => m!"{toEmoji cfg.eraseProofs} Erase Proofs"
      trace cls fun _ => m!"{toEmoji cfg.eraseLambdaDomains} Erase λ's Domains"
      trace cls fun _ => m!"{toEmoji cfg.eraseForallDomains} Erase ∀'s Domains"
    withTraceNode cls (fun _ => return "Debug") (collapsed := false) do
      trace cls fun _ => m!"Exit Point: {cfg.exitPoint.format}"
      trace cls fun _ => m!"E-Graph Visualization Export Path: {cfg.vizPath.getD "None"}"
      trace cls fun _ => m!"{toEmoji cfg.traceSubstitutions} Trace Substitutions"
      trace cls fun _ => m!"{toEmoji cfg.traceBVarCorrection} Trace BVar Index Correction"

nonrec def Request.trace (req : Request) (cls : Name) : TacticM Unit := do
  withTraceNode cls (fun _ => return "Goal") do
    trace cls fun _ => m!"LHS: {req.lhs}"
    trace cls fun _ => m!"RHS: {req.rhs}"
  let rwsHeader := s!"{if req.rws.isEmpty then "No " else ""}Rewrites"
  withTraceNode `egg.frontend (fun _ => return rwsHeader) do
    for rw in req.rws do
      rw.trace cls
  if !req.guides.isEmpty then
    withTraceNode cls (fun _ => return "Guides") do
      for guide in req.guides do
        trace cls fun _ => guide

nonrec def Proof.trace (prf : Proof) (cls : Name) : TacticM Unit := do
  withTraceNode cls (fun _ => return "Proof") do
    for step in prf, idx in [:prf.size] do
      if idx == 0 then trace cls fun _ => step.lhs
      match step.rw with
      | .defeq src =>
        if src.isNatLitConversion then continue
        withTraceNode cls (fun _ => return step.rhs) do
          trace cls fun _ => m!"{src.description}({dirFormat step.dir})"
      | .rw rw _ =>
        if rw.src.containsTcProj then continue
        withTraceNode cls (fun _ => return step.rhs) do
          traceM cls fun _ => return m!"{rw.src.description}({dirFormat step.dir}) {← rw.toCongr.format}"
          trace  cls fun _ => step.proof
where
  dirFormat : Direction → Format
    | .forward  => "⇒"
    | .backward => "⇐"

nonrec def MVars.Ambient.trace (amb : MVars.Ambient) (cls : Name) : TacticM Unit := do
  withTraceNode cls (fun _ => return "Ambient MVars") do
    for m in ← amb.unassigned do
      trace cls fun _ => m!"{Expr.mvar m}"
