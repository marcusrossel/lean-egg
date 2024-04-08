import Egg.Core.Encode.Rewrites
import Egg.Core.Config
import Egg.Core.Gen.Explosion
import Egg.Core.Explanation.Basic
import Egg.Core.Rewrites.Basic
open Lean

namespace Egg.Request

protected structure Config where
  optimizeExpl        : Bool
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
    genNatLitRws        := cfg.genNatLitRws
    genEtaRw            := cfg.genEtaRw
    genBetaRw           := cfg.genBetaRw
    blockInvalidMatches := cfg.blockInvalidMatches
    shiftCapturedBVars  := cfg.shiftCapturedBVars
    traceSubstitutions  := cfg.traceSubstitutions
    traceBVarCorrection := cfg.traceBVarCorrection
  }

structure _root_.Egg.Request where
  private mk ::
  lhs     : Expression
  rhs     : Expression
  rws     : Rewrites.Encoded
  vizPath : String
  cfg     : Request.Config

def encoding (goal : Congr) (rws : Rewrites) (cfg : Egg.Config) : MetaM Request := do
  return {
    lhs := ← encode goal.lhs .goal cfg.toEncoding
    rhs := ← encode goal.rhs .goal cfg.toEncoding
    rws := ← rws.encode cfg.toEncoding
    vizPath := cfg.vizPath.getD ""
    cfg
  }

@[extern "lean_egg_explain_congr"]
private opaque explainCongr
  (lhs rhs : Expression) (rws : Rewrites.Encoded) (vizPath : String) (cfg : Request.Config) : String

def run (req : Request) : Explanation.Raw :=
  explainCongr req.lhs req.rhs req.rws req.vizPath req.cfg
