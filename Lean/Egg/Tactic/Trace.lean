import Egg.Core.Request.Basic
import Egg.Core.Explanation.Proof
import Egg.Tactic.Premises.Parse
import Lean
open Lean Meta Elab Tactic Std Format

initialize registerTraceClass `egg
initialize registerTraceClass `egg.config            (inherited := true)
initialize registerTraceClass `egg.rewrites          (inherited := true)
initialize registerTraceClass `egg.ambient           (inherited := true)
initialize registerTraceClass `egg.encoded           (inherited := true)
initialize registerTraceClass `egg.explanation       (inherited := true)
initialize registerTraceClass `egg.explanation.steps (inherited := true)
initialize registerTraceClass `egg.proof             (inherited := true)
initialize registerTraceClass `egg.proof.term        (inherited := false)

namespace Egg

def Direction.format : Direction → Format
  | .forward  => "⇒"
  | .backward => "⇐"

def Explanation.involvesBinderRewrites (expl : Explanation) : Bool :=
  expl.steps.any (·.src.involvesBinders)

def Config.Debug.ExitPoint.format : Config.Debug.ExitPoint → Format
  | .none        => "None"
  | .beforeEqSat => "Before Equality Saturation"
  | .beforeProof => "Before Proof Reconstruction"

nonrec def formatReport
    (flat : Bool) (rep : Request.Result.Report) (totalDuration? proofDuration? : Option Nat := none)
    (expl? : Option Explanation := none) : Format :=
  if flat then
    "(" ++ (if let some d := totalDuration? then format d else "-") ++ "," ++
    (format <| (1000 * rep.time).toUInt64.toNat) ++ "," ++
    (if let some d := proofDuration? then format d else "-") ++ "," ++ (format rep.iterations) ++
    "," ++ (format rep.nodeCount) ++ "," ++ (format rep.classCount) ++ "," ++
    (if let some e := expl? then format e.steps.size ++ s!",{e.involvesBinderRewrites}" else "-,-")
    ++ ")"
  else
    (if let some d := totalDuration? then "\ntotal time: " ++ format d ++ "ms\n" else "") ++
    "eqsat time: " ++ (format <| (1000 * rep.time).toUInt64.toNat) ++ "ms\n" ++
    (if let some d := proofDuration? then "proof time: " ++ format d ++ "ms\n" else "") ++
    "iters:      " ++ (format rep.iterations) ++ "\n" ++
    "nodes:      " ++ (format rep.nodeCount)  ++ "\n" ++
    "classes:    " ++ (format rep.classCount) ++ "\n" ++
    (if let some e := expl? then "expl steps: " ++ format e.steps.size ++ s!"\nbinder rws: {e.involvesBinderRewrites}\n" else "") ++
    (if rep.rwStats.isEmpty then "" else s!"\nrw stats:\n{rep.rwStats}")

def MVars.Property.toMessageData : MVars.Property → MessageData
  | .unconditionallyVisible => m!".unconditionallyVisible"
  | .isTcInst               => m!".isTcInst"
  | .inTcInstTerm           => m!".inTcInstTerm"
  | .inErasedTcInst         => m!".inErasedTcInst"
  | .inProofTerm            => m!".inProofTerm"
  | .inErasedProof          => m!".inErasedProof"
  | .inEqType               => m!".inEqType"

def MVars.Properties.toMessageData (ps : MVars.Properties) : MessageData :=
  ps.toList.map Property.toMessageData

nonrec def MVars.toMessageData (mvars : MVars) : MetaM MessageData := do
  let mut data := []
  for (mvar, ps) in mvars.expr do data := data.concat m!"{← ppExpr <| .mvar mvar}: {ps.toMessageData}"
  for (mvar, ps) in mvars.lvl  do data := data.concat m!"{Level.mvar mvar}: {ps.toMessageData}"
  return data

def Directions.format : Directions → Format
  | .none     => "∅"
  | .forward  => "⇒"
  | .backward => "⇐"
  | .both     => "⇔"

def Congr.Rel.format : Congr.Rel → Format
  | .eq  => "="
  | .iff => "↔"

def Congr.toMessageData (cgr : Congr) : MetaM MessageData :=
  return (← ppExpr cgr.lhs) ++ " " ++ cgr.rel.format ++ " " ++ (← ppExpr cgr.rhs)

def Rewrite.trace (rw : Rewrite) (stx? : Option Syntax) (cls : Name) : TacticM Unit := do
  let mut header := m!"{rw.src.description}({rw.validDirs.format})"
  if let some stx := stx? then header := m!"{header}: {stx}"
  withTraceNode cls (fun _ => return header) do
    traceM cls fun _ => rw.toCongr.toMessageData
    if !rw.conds.isEmpty then
      withTraceNode cls (fun _ => return "Conditions") (collapsed := false) do
        for cond in rw.conds.filter (!·.isProven) do
          traceM cls fun _ => return m!"{cond.type}"
        if !(rw.conds.filter (·.isProven)).isEmpty then
          withTraceNode cls (fun _ => return "Proven") (collapsed := true) do
            for cond in rw.conds.filter (·.isProven) do
              traceM cls fun _ => return m!"{cond.type}"
    traceM cls fun _ => return m!"LHS MVars\n{← rw.mvars.lhs.toMessageData}"
    traceM cls fun _ => return m!"RHS MVars\n{← rw.mvars.rhs.toMessageData}"

def Rewrites.trace (rws : Rewrites) (stx : Array Syntax) (cls : Name) : TacticM Unit := do
  for rw in rws, idx in [:rws.size] do
    let stx? := stx[idx]? >>= fun s => if s.getAtomVal == "*" then none else s
    rw.trace stx? cls

def Rewrite.Encoded.trace (rw : Rewrite.Encoded) (cls : Name) : TacticM Unit := do
  let header := m!"{rw.name}({rw.dirs.format})"
  withTraceNode cls (fun _ => return header) do
    Lean.trace cls fun _ => m!"LHS: {rw.lhs}"
    Lean.trace cls fun _ => m!"RHS: {rw.rhs}"
    if rw.conds.isEmpty then
      Lean.trace cls fun _ => "No Conditions"
    else
      withTraceNode cls (fun _ => return "Conditions") (collapsed := false) do
        for cond in rw.conds do
          Lean.trace cls fun _ => cond

nonrec def Config.trace (cfg : Config) (cls : Name) : TacticM Unit := do
  let toEmoji (b : Bool) := if b then "✅" else "❌"
  withTraceNode cls (fun _ => return "Configuration") do
    trace cls fun _ => m!"{toEmoji cfg.genTcProjRws} Generate Type Class Projection Rewrites"
    trace cls fun _ => m!"{toEmoji cfg.genTcSpecRws} Generate Type Class Specialization Rewrites"
    trace cls fun _ => m!"{toEmoji cfg.natLit} Enable Definitional Natural Number Literal Rewrites"
    trace cls fun _ => m!"{toEmoji cfg.beta} Enable β-Reduction"
    trace cls fun _ => m!"{toEmoji cfg.eta} Enable η-Reduction"
    trace cls fun _ => m!"{toEmoji cfg.blockInvalidMatches} Block Invalid Matches"
    trace cls fun _ => m!"{toEmoji cfg.shiftCapturedBVars} Correct BVar Indices"
    trace cls fun _ => m!"{toEmoji cfg.optimizeExpl} Optimize Explanation Length"
    withTraceNode cls (fun _ => return "Encoding") (collapsed := false) do
      trace cls fun _ => m!"{toEmoji cfg.betaReduceRws} β-Reduce Rewrites"
      trace cls fun _ => m!"{toEmoji cfg.etaReduceRws} η-Reduces Rewrites"
    withTraceNode cls (fun _ => return "Debug") (collapsed := false) do
      trace cls fun _ => m!"Exit Point: {cfg.exitPoint.format}"
      trace cls fun _ => m!"E-Graph Visualization Export Path: {cfg.vizPath.getD "None"}"

nonrec def Config.DefEq.trace (cfg : Config.DefEq) (cls : Name) : TacticM Unit := do
  withTraceNode cls (fun _ => return "Definitional") do
    if cfg.beta      then Lean.trace cls fun _ => "β-Reduction"
    if cfg.eta       then Lean.trace cls fun _ => "η-Reduction"
    if cfg.etaExpand then Lean.trace cls fun _ => "η-Expansion"
    if cfg.natLit    then Lean.trace cls fun _ => "Natural Number Literals"
    if cfg.levels    then Lean.trace cls fun _ => "Universe Levels"

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

nonrec def Explanation.trace (expl : Explanation) (cls : Name) : TacticM Unit := do
  withTraceNode cls (fun _ => return "Explanation Steps") do
    trace cls fun _ => m!"{expl.start}"
    for step in expl.steps, idx in [:expl.steps.size] do
      withTraceNode cls (fun _ => return m!"{idx}: {step.dst}") do
        trace cls fun _ => m!"{step.src.description}({step.dir.format})"

nonrec def Proof.trace (prf : Proof) (cls : Name) : TacticM Unit := do
  withTraceNode cls (fun _ => return "Proof") do
    for step in prf, idx in [:prf.size] do
      if idx == 0 then
        let lhs ← instantiateMVars step.lhs
        trace cls fun _ => lhs
      match step.rw with
      | .defeq src =>
        if src.isNatLitConversion || src.isSubst then continue
        withTraceNode cls (fun _ => instantiateMVars step.rhs) do
          trace cls fun _ => m!"{src.description}({step.dir.format})"
      | .rw rw _ =>
        if rw.src.containsTcProj then continue
        withTraceNode cls (fun _ => instantiateMVars step.rhs) do
          traceM cls fun _ => return m!"{rw.src.description}({step.dir.format}) {← rw.toCongr.toMessageData}"
          trace  cls fun _ => step.proof
      | .reifiedEq =>
        withTraceNode cls (fun _ => instantiateMVars step.rhs) do
          trace cls fun _ => m!"Reified Equality"
      | .factAnd =>
        withTraceNode cls (fun _ => instantiateMVars step.rhs) do
          trace cls fun _ => m!"Fact ∧ Fact"
