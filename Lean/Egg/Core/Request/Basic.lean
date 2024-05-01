import Egg.Core.Encode.Rewrites
import Egg.Core.Encode.Guides
import Egg.Core.Encode.Facts
import Egg.Core.Config
import Egg.Core.Explanation.Basic
open Lean

namespace Egg.Request

-- IMPORTANT: The C interface to egg depends on the order of these fields.
protected structure Config where
  optimizeExpl        : Bool
  timeLimit           : Nat
  genNatLitRws        : Bool
  genEtaRw            : Bool
  genBetaRw           : Bool
  blockInvalidMatches : Bool
  shiftCapturedBVars  : Bool
  traceSubstitutions  : Bool
  traceBVarCorrection : Bool

instance : Coe Config Request.Config where
  coe cfg := {
    optimizeExpl        := cfg.optimizeExpl
    timeLimit           := cfg.timeLimit
    genNatLitRws        := cfg.genNatLitRws
    genEtaRw            := cfg.genEtaRw
    genBetaRw           := cfg.genBetaRw
    blockInvalidMatches := cfg.blockInvalidMatches
    shiftCapturedBVars  := cfg.shiftCapturedBVars
    traceSubstitutions  := cfg.traceSubstitutions
    traceBVarCorrection := cfg.traceBVarCorrection
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
    (goal : Congr) (rws : Rewrites) (facts : Facts) (guides : Guides) (cfg : Egg.Config)
    (amb : MVars.Ambient) : MetaM Request := do
  return {
    lhs     := ← encode goal.lhs cfg amb
    rhs     := ← encode goal.rhs cfg amb
    rws     := ← rws.encode cfg amb
    facts   := if rws.any (·.isConditional) then ← facts.encode cfg amb else #[]
    guides  := ← guides.encode cfg amb
    vizPath := cfg.vizPath.getD ""
    cfg
  }

@[extern "run_egg_request_pure"]
opaque run' (req : Request) : Explanation.Raw
