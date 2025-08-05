import Egg.Core.Request.Basic
import Egg.Core.Explanation.Proof
import Egg.Tactic.Premises.Parse
import Lean
open Lean Meta Elab Tactic Std Format

initialize registerTraceClass `egg
initialize registerTraceClass `egg.config                (inherited := true)
initialize registerTraceClass `egg.rewrites              (inherited := true)
initialize registerTraceClass `egg.rewrites.intro        (inherited := true)
initialize registerTraceClass `egg.rewrites.explicit     (inherited := true)
initialize registerTraceClass `egg.rewrites.goalTypeSpec (inherited := true)
initialize registerTraceClass `egg.rewrites.explosion    (inherited := true)
initialize registerTraceClass `egg.rewrites.tcProj       (inherited := true)
initialize registerTraceClass `egg.rewrites.structProj   (inherited := true)
initialize registerTraceClass `egg.rewrites.builtin      (inherited := true)
initialize registerTraceClass `egg.rewrites.baskets      (inherited := true)
initialize registerTraceClass `egg.rewrites.pruned       (inherited := true)
initialize registerTraceClass `egg.guides                (inherited := true)
initialize registerTraceClass `egg.encoded               (inherited := true)
initialize registerTraceClass `egg.explanation           (inherited := true)
initialize registerTraceClass `egg.explanation.steps     (inherited := true)
initialize registerTraceClass `egg.proof                 (inherited := true)
initialize registerTraceClass `egg.proof.term            (inherited := false)
initialize registerTraceClass `egg.activations           (inherited := true)

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

def MVars.Property.toString : MVars.Property → String
  | .unconditionallyVisible => "unconditionallyVisible"
  | .isTcInst               => "isTcInst"
  | .inTcInstTerm           => "inTcInstTerm"
  | .inErasedTcInst         => "inErasedTcInst"
  | .isProof                => "isProof"
  | .inProofTerm            => "inProofTerm"
  | .inErasedProof          => "inErasedProof"
  | .inEqType               => "inEqType"

def MVars.Properties.toMessageData (ps : MVars.Properties) : MessageData :=
  ps.toList.map Property.toString |>.mergeSort |>.map (m!"{·}")

nonrec def MVars.toMessageData (mvars : MVars) : MetaM MessageData := do
  let mut data := []
  for (mvar, ps) in mvars.expr.toList.mergeSort (·.fst.name.toString ≤ ·.fst.name.toString) do data := data.concat m!"{Expr.mvar mvar}: {ps.toMessageData}"
  for (mvar, ps) in mvars.lvl.toList.mergeSort (·.fst.name.toString ≤ ·.fst.name.toString)  do data := data.concat m!"{Level.mvar mvar}: {ps.toMessageData}"
  return data

def Congr.Rel.format : Congr.Rel → Format
  | .eq  => "="
  | .iff => "↔"

def Congr.toMessageData (cgr : Congr) : MetaM MessageData :=
  return cgr.lhs ++ " " ++ cgr.rel.format ++ " " ++ cgr.rhs

def Rewrite.Violation.toMessageData : Rewrite.Violation → MessageData
  | rhsMVarInclusion missing => m!"rhsMVarInclusion: {missing.toList.map Expr.mvar}"
  | rhsUVarInclusion missing => m!"rhsUVarInclusion: {missing.toList.map Level.mvar}"
  | lhsSingleMVar _          => "lhsSingleMVar"
  | covering missing         => m!"covering: {missing.toList.map Expr.mvar}"
  | tcMVarInclusion missing  => m!"tcMVarInclusion: {missing.toList.map Expr.mvar}"
  | tcUVarInclusion          => "tcUVarInclusion"
  | unsynthesizable ms       => m!"unsynthesizable: {ms.toList.map Expr.mvar}"

def Rewrite.trace (rw : Rewrite) (stx? : Option Syntax) (cls : Name) (subgoals : Bool)
    (headerAnnotation : String := "") : TacticM Unit := do
  let violations := (← rw.violations subgoals).map (·.toMessageData)
  let violations := if violations.isEmpty then MessageData.nil else m!"❌{violations}"
  let mut header := m!"{rw.src.description}({rw.dir.format}){violations}{headerAnnotation}"
  if let some stx := stx? then header := m!"{header}: {stx}"
  withTraceNode cls (fun _ => return header) do
    traceM cls fun _ => rw.toCongr.toMessageData
    unless rw.conds.active.isEmpty do
      withTraceNode cls (fun _ => return "Conditions") (collapsed := false) do
        for cond in rw.conds.active do
          traceM cls fun _ => return m!"{cond.type}"
    traceM cls fun _ => return m!"LHS MVars\n{← rw.mvars.lhs.toMessageData}"
    traceM cls fun _ => return m!"RHS MVars\n{← rw.mvars.rhs.toMessageData}"

def Rewrites.trace (rws : Rewrites) (stx : Array Syntax) (cls : Name) (subgoals : Bool) :
    TacticM Unit := do
  for rw in rws, idx in [:rws.size] do
    let stx? := stx[idx]? >>= fun s => if s.getAtomVal == "*" then none else s
    rw.trace stx? cls subgoals

def Rewrites.tracePruned
    (rws : Rewrites) (reasons : Array Source) (cls : Name) (subgoals : Bool) :
    TacticM Unit := do
  for rw in rws, reason in reasons do
    rw.trace (stx? := none) cls subgoals (headerAnnotation := s!" by {reason.description}")

def Rewrite.Encoded.trace (rw : Rewrite.Encoded) (cls : Name) : TacticM Unit := do
  let header := m!"{rw.name}"
  withTraceNode cls (fun _ => return header) do
    Lean.trace cls fun _ => m!"LHS: {rw.lhs}"
    Lean.trace cls fun _ => m!"RHS: {rw.rhs}"
    if rw.conds.isEmpty then
      Lean.trace cls fun _ => "No Conditions"
    else
      withTraceNode cls (fun _ => return "Conditions") (collapsed := false) do
        for cond in rw.conds do
          Lean.trace cls fun _ => cond

def _root_.Bool.toEmoji : Bool → String
  | true  => "✅"
  | false => "❌"

nonrec def Config.Encoding.trace (cfg : Config.Encoding) (cls : Name) (collapsed := true) : TacticM Unit := do
  withTraceNode cls (fun _ => return "Encoding") (collapsed := collapsed) do
    trace cls fun _ => m!"{cfg.shapes.toEmoji} Shapes"
    trace cls fun _ => m!"{cfg.betaReduceRws.toEmoji} β-Reduce Rewrites"
    trace cls fun _ => m!"{cfg.etaReduceRws.toEmoji} η-Reduces Rewrites"

nonrec def Config.DefEq.trace (cfg : Config.DefEq) (cls : Name) (collapsed := true) : TacticM Unit := do
  withTraceNode cls (fun _ => return "Definitional") (collapsed := collapsed) do
    trace cls fun _ => m!"{cfg.beta.toEmoji} β-Reduction"
    trace cls fun _ => m!"{cfg.eta.toEmoji} η-Reduction"
    trace cls fun _ => m!"{cfg.etaExpand.toEmoji} η-Expansion"
    trace cls fun _ => m!"{cfg.natLit.toEmoji} Natural Number Literals"
    trace cls fun _ => m!"{cfg.levels.toEmoji} Universe Levels"

nonrec def Config.Gen.trace (cfg : Config.Gen) (cls : Name) (collapsed := true) : TacticM Unit := do
  withTraceNode cls (fun _ => return "Generation") (collapsed := collapsed) do
    trace cls fun _ => m!"{cfg.builtins.toEmoji} Builtins"
    trace cls fun _ => m!"{cfg.structProjs.toEmoji} Structure Projections"
    trace cls fun _ => m!"{cfg.tcProjs.toEmoji} Type Class Projections"
    trace cls fun _ => m!"{cfg.goalTypeSpec.toEmoji} Goal Type Specializations"
    trace cls fun _ => m!"{cfg.groundEqs.toEmoji} Ground Equations"
    trace cls fun _ => m!"{cfg.derivedGuides.toEmoji} Derived Guides"
    trace cls fun _ => m!"{cfg.explosion.toEmoji} Explosion"

nonrec def Config.Backend.trace (cfg : Config.Backend) (cls : Name) (collapsed := true) : TacticM Unit := do
  withTraceNode cls (fun _ => return "Generation") (collapsed := collapsed) do
    trace cls fun _ => m!"{cfg.unionSemantics.toEmoji} Union Semantics"
    trace cls fun _ => m!"{cfg.optimizeExpl.toEmoji} Optimize Explanation Length"
    trace cls fun _ => m!"Time Limit: {cfg.timeLimit}"
    trace cls fun _ => m!"E-Node Limit: {cfg.nodeLimit}"
    trace cls fun _ => m!"Iteration Limit: {cfg.iterLimit}"

nonrec def Config.trace (cfg : Config) (cls : Name) : TacticM Unit := do
  withTraceNode cls (fun _ => return "Configuration") do
    Encoding.trace cfg cls (collapsed := false)
    DefEq.trace cfg.toDefEq cls (collapsed := false)
    Gen.trace cfg.toGen cls (collapsed := false)
    Backend.trace cfg.toBackend cls (collapsed := false)

nonrec def Guide.trace (guide : Guide) (cls : Name) : TacticM Unit := do
  trace cls fun _ => m!"{guide.src.description}: " ++ guide.expr

def Guides.trace (guides : Guides) (cls : Name) : TacticM Unit := do
  for guide in guides do guide.trace cls

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
