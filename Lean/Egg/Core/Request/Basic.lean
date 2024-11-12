import Egg.Core.Request.EGraph
import Egg.Core.Encode.Rewrites
import Egg.Core.Encode.Guides
import Egg.Core.Encode.Facts
import Egg.Core.Config
import Egg.Core.Explanation.Parse.Basic
open Lean

namespace Egg.Request

-- IMPORTANT: The C interface to egg depends on the order of these fields.
protected structure Config where
  slotted              : Bool
  optimizeExpl         : Bool
  timeLimit            : Nat
  nodeLimit            : Nat
  iterLimit            : Nat
  natLit         : Bool
  eta             : Bool
  beta            : Bool
  levels          : Bool
  shapes               : Bool
  blockInvalidMatches  : Bool
  shiftCapturedBVars   : Bool
  unionSemantics       : Bool
  allowUnsatConditions : Bool

instance : Coe Config Request.Config where
  coe cfg := {
    slotted              := cfg.slotted
    optimizeExpl         := cfg.optimizeExpl
    timeLimit            := cfg.timeLimit
    nodeLimit            := cfg.nodeLimit
    iterLimit            := cfg.iterLimit
    natLit         := cfg.natLit
    eta             := cfg.eta
    beta            := cfg.beta
    levels          := cfg.levels
    shapes               := cfg.shapes
    blockInvalidMatches  := cfg.blockInvalidMatches
    shiftCapturedBVars   := cfg.shiftCapturedBVars
    unionSemantics       := cfg.unionSemantics
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

-- Returns the encoded request with a flag indicating whether the proof goal contains a binder.
def encoding'
    (goal : Congr) (rws : Rewrites) (facts : Facts) (guides : Guides) (cfg : Config)
    (amb : MVars.Ambient) : MetaM (Request × Bool) := do
  let ctx := { cfg, amb }
  let (lhs, lhsBinder) ← encode' goal.lhs ctx
  let (rhs, rhsBinder) ← encode' goal.rhs ctx
  let req := {
    lhs, rhs
    rws     := ← rws.encode ctx
    facts   := ← do if rws.any (·.isConditional) then facts.encode ctx else return #[]
    guides  := ← guides.encode ctx
    vizPath := cfg.vizPath.getD ""
    cfg
  }
  return (req, lhsBinder || rhsBinder)

def encoding (goal : Congr) (rws : Rewrites) (facts : Facts) (guides : Guides) (cfg : Config)
    (amb : MVars.Ambient) : MetaM Request :=
  Prod.fst <$> encoding' goal rws facts guides cfg amb

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
  expl    : String
  egraph? : Option EGraph.Obj
  report? : Option Report
  deriving Inhabited

@[extern "run_eqsat_request"]
private opaque runRaw (req : Request) : Result.Raw

structure Result where
  expl   : Explanation
  egraph : EGraph
  report : Result.Report

inductive Failure where
  | backend
  | explLength (len : Nat)

def run
    (req : Request) (explLengthLimit : Nat) (onFail : Result.Report → Failure → MetaM MessageData) :
    MetaM Result := do
  let raw := runRaw req
  withTraceNode `egg.explanation (fun _ => return "Explanation") do trace[egg.explanation] raw.expl
  if "⚡️".isPrefixOf raw.expl then
    throwError s!"egg backend failed:\n  {raw.expl}"
  else
    let some report := raw.report? | throwError "egg: internal error: report is absent"
    if raw.expl.isEmpty then
      throwError ← onFail report .backend
    else
      let explLength := raw.expl.lineCount
      if explLength > explLengthLimit then
        throwError ← onFail report (.explLength explLength)
      else
        let some obj := raw.egraph? | throwError "egg: internal error: e-graph is absent"
        let egraph := { obj, slotted := req.cfg.slotted }
        let expl ← Explanation.Raw.parse { str := raw.expl, slotted := req.cfg.slotted }
        return { expl, egraph, report }
