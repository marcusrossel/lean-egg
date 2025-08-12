import Egg.Core.Request.EGraph
import Egg.Core.Encode.Rules
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
    unionSemantics       := cfg.unionSemantics
    allowUnsatConditions := cfg.subgoals
  }

-- IMPORTANT: The C interface to egg depends on the order of these fields.
structure _root_.Egg.Request where
  private mk ::
  lhs     : Expression
  rhs     : Expression
  rws     : Rewrite.Rules.Encoded
  guides  : Guides.Encoded
  vizPath : String
  cfg     : Request.Config

-- TODO: We bump the mctx depth for objects which should not contain pattern variables. This is used
--       to ensure that *level* mvars do not get encoded as pattern variables, as `Egg.eval.core`
--       sets the `allowLevelAssignments` option on `withNewMCtxDepth` to `true`, and here we set it
--       to (the default value) `false`. We could just set the `allowLevelAssignments` to `false`
--       in the first place, but that seems to cause problems when encoding rewrites. I'm not sure
--       why though, and I think it has to do with how universe levels are elaborated.
def encoding (goal : Congr) (rules : Rewrite.Rules) (guides : Guides) (cfg : Config) : MetaM Request :=
  return {
    lhs     := ← Meta.withNewMCtxDepth do encode goal.lhs cfg
    rhs     := ← Meta.withNewMCtxDepth do encode goal.rhs cfg
    rws     := ← rules.encode cfg cfg.subgoals
    guides  := ← Meta.withNewMCtxDepth do guides.encode cfg
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
  iterations  : Nat
  stopReason  : StopReason
  reasonMsg   : String
  nodeCount   : Nat
  classCount  : Nat
  time        : Float
  rwStats     : String
  activations : String
deriving Inhabited

-- IMPORTANT: The C interface to egg depends on the order of these constructors.
private inductive Explanation.Kind.Raw where
  | none
  | sameEClass
  | eqTrue
deriving Inhabited

private def Explanation.Kind.Raw.toKind? : Raw → Option Explanation.Kind
  | none       => .none
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
  withTraceNode `egg.activations (fun _ => return "Activations") do trace[egg.activations] raw.report.activations
  let some kind := raw.kind.toKind? | throwError ← onFail raw.report (.backend raw.expl)
  let explLength := raw.expl.lineCount
  unless explLength <= explLengthLimit do throwError ← onFail raw.report (.explLength explLength)
  let some obj := raw.egraph? | throwError "egg: internal error: e-graph is absent"
  let egraph := { obj, slotted := req.cfg.slotted }
  let expl ← Explanation.Raw.parse { kind, str := raw.expl, slotted := req.cfg.slotted }
  return { expl, egraph, report := raw.report }
