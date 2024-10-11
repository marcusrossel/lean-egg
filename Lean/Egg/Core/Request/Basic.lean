import Egg.Core.Request.EGraph
import Egg.Core.Encode.Rewrites
import Egg.Core.Encode.Guides
import Egg.Core.Encode.Facts
import Egg.Core.Config
import Egg.Core.Explanation.Parse
open Lean

namespace Egg.Request

-- IMPORTANT: The C interface to egg depends on the order of these fields.
protected structure Config where
  optimizeExpl         : Bool
  timeLimit            : Nat
  nodeLimit            : Nat
  iterLimit            : Nat
  genNatLitRws         : Bool
  genEtaRw             : Bool
  genBetaRw            : Bool
  genLevelRws          : Bool
  allowUnsatConditions : Bool

instance : Coe Config Request.Config where
  coe cfg := {
    optimizeExpl         := cfg.optimizeExpl
    timeLimit            := cfg.timeLimit
    nodeLimit            := cfg.nodeLimit
    iterLimit            := cfg.iterLimit
    genNatLitRws         := cfg.genNatLitRws
    genEtaRw             := cfg.genEtaRw
    genBetaRw            := cfg.genBetaRw
    genLevelRws          := cfg.genLevelRws
    allowUnsatConditions := cfg.conditionSubgoals
  }

-- IMPORTANT: The C interface to egg depends on the order of these fields.
structure _root_.Egg.Request where
  private mk ::
  lhs     : Expression
  rhs     : Expression
  rws     : Rewrites.Encoded
  facts   : Facts.Encoded
  guides  : Guides.Encoded
  vizPath : String
  cfg     : Request.Config

def encoding
    (goal : Congr) (rws : Rewrites) (facts : Facts) (guides : Guides) (cfg : Config)
    (amb : MVars.Ambient) : MetaM Request :=
  let ctx := { cfg, amb }
  return {
    lhs     := ← encode goal.lhs ctx
    rhs     := ← encode goal.rhs ctx
    rws     := ← rws.encode ctx
    facts   := ← do if rws.any (·.isConditional) then facts.encode ctx else return #[]
    guides  := ← guides.encode ctx
    vizPath := cfg.vizPath.getD ""
    cfg
  }

-- IMPORTANT: The C interface to egg depends on the order of these constructors.
inductive Result.StopReason where
  | saturated
  | timeLimit
  | iterationLimit
  | nodeLimit
  | other

def Result.StopReason.description : StopReason → String
  | saturated      => "saturated"
  | timeLimit      => "reached time limit"
  | iterationLimit => "reached iteration limit"
  | nodeLimit      => "reached node limit"
  | other          => "unknown reason"


-- IMPORTANT: The C interface to egg depends on the order of these fields.
structure Result.Report where
  iterations:  Nat
  stopReason:  StopReason
  nodeCount:   Nat
  classCount:  Nat
  time:        Float

-- IMPORTANT: The C interface to egg depends on the order of these fields.
private structure Result.Raw where
  expl    : Explanation.Raw
  egraph? : Option EGraph
  report? : Option Report
  deriving Inhabited

@[extern "run_egg_request"]
private opaque runRaw (req : Request) : Result.Raw

structure Result where
  expl   : Explanation
  egraph : EGraph
  report : Result.Report

def run (req : Request) (onFail : Result.Report → MetaM Result) : MetaM Result := do
  let raw := runRaw req
  withTraceNode `egg.explanation (fun _ => return "Explanation") do trace[egg.explanation] raw.expl
  if "⚡️".isPrefixOf raw.expl then
    throwError s!"egg backend failed:\n  {raw.expl}"
  else
    let some report := raw.report? | throwError "egg: internal error: report is absent"
    if raw.expl.isEmpty then
      onFail report
    else
      let some egraph := raw.egraph? | throwError "egg: internal error: e-graph is absent"
      return { expl := ← raw.expl.parse, egraph, report }

structure Result' where
  expl   : String
  egraph : EGraph
  report : Result.Report

def run' (req : Request) (onFail : Result.Report → MetaM Result') : MetaM Result' := do
  let raw := runRaw req
  withTraceNode `egg.explanation (fun _ => return "Explanation") do trace[egg.explanation] raw.expl
  if "⚡️".isPrefixOf raw.expl then
    throwError s!"egg backend failed:\n  {raw.expl}"
  else
    let some report := raw.report? | throwError "egg: internal error: report is absent"
    if raw.expl.isEmpty then
      onFail report
    else
      let some egraph := raw.egraph? | throwError "egg: internal error: e-graph is absent"
      return { expl := raw.expl, egraph, report }
