import Egg.Core.Request.EGraph
import Egg.Core.Encode.Rewrites
import Egg.Core.Encode.Guides
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
  natLit               : Bool
  eta                  : Bool
  etaExpand            : Bool
  beta                 : Bool
  levels               : Bool
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
    natLit               := cfg.natLit
    eta                  := cfg.eta
    etaExpand            := cfg.etaExpand
    beta                 := cfg.beta
    levels               := cfg.levels
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
  guides  : Guides.Encoded
  vizPath : String
  cfg     : Request.Config

def encoding (goal : Congr) (rws : Rewrites) (guides : Guides) (cfg : Config) : MetaM Request :=
  return {
    lhs     := ← encode goal.lhs cfg
    rhs     := ← encode goal.rhs cfg
    rws     := ← rws.encode cfg
    guides  := ← guides.encode cfg
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
  deriving Inhabited

def Result.StopReason.description : StopReason → String
  | saturated      => "saturated"
  | timeLimit      => "reached time limit"
  | iterationLimit => "reached iteration limit"
  | nodeLimit      => "reached node limit"
  | other          => "unknown reason"

-- IMPORTANT: The C interface to egg depends on the order of these fields.
structure Result.Report where
  iterations: Nat
  stopReason: StopReason
  reasonMsg:  String
  nodeCount:  Nat
  classCount: Nat
  time:       Float
  rwStats:    String
  deriving Inhabited

-- IMPORTANT: The C interface to egg depends on the order of these constructors.
private inductive Explanation.Kind.Raw where
  | none
  | sameEClass
  | eqTrue
  deriving Inhabited

private def Explanation.Kind.Raw.toKind? : Raw → Option Explanation.Kind
  | none       => Option.none
  | sameEClass => some .sameEClass
  | eqTrue     => some .eqTrue

-- IMPORTANT: The C interface to egg depends on the order of these fields.
structure Result.Raw where
  kind    : Explanation.Kind.Raw
  expl    : String
  egraph? : Option EGraph.Obj
  report  : Report
  deriving Inhabited

@[extern "run_eqsat_request"]
private opaque runRaw (req : Request) : MetaM Result.Raw

structure Result where
  expl   : Explanation
  egraph : EGraph
  report : Result.Report

inductive Failure where
  | backend (msg : String)
  | explLength (len : Nat)

def run
    (req : Request) (explLengthLimit : Nat) (onFail : Result.Report → Failure → MetaM MessageData) :
    MetaM Result := do
  let raw ← runRaw req
  withTraceNode `egg.explanation (fun _ => return "Explanation") do trace[egg.explanation] raw.expl
  let some kind := raw.kind.toKind? | throwError ← onFail raw.report (.backend raw.expl)
  let explLength := raw.expl.lineCount
  unless explLength <= explLengthLimit do throwError ← onFail raw.report (.explLength explLength)
  let some obj := raw.egraph? | throwError "egg: internal error: e-graph is absent"
  let egraph := { obj, slotted := req.cfg.slotted }
  let expl ← Explanation.Raw.parse { kind, str := raw.expl, slotted := req.cfg.slotted }
  return { expl, egraph, report := raw.report }
