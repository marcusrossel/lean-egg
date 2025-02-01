import Egg.Core.Encode.Basic
import Egg.Core.Explanation.Basic
import Egg.Core.Request.Basic
import Egg.Core.Request.EGraph
import Lean
open Lean

namespace Egg.Request

structure Equiv where
  init : Expression
  goal : Expression

def Equiv.encoding (init goal : Expr) (cfg : Config.Encoding) : MetaM Equiv :=
  return { init := ← encode init cfg, goal := ← encode goal cfg }

end Request

@[extern "explain_equiv"]
private opaque explainEquivRaw (graph : EGraph.Obj) (slotted : Bool) (e₁ e₂ : Expression) : Request.Result.Raw

def EGraph.run (graph : EGraph) (req : Request.Equiv) : Option Explanation.Raw := Id.run do
  let { kind := kind?, expl, .. } := explainEquivRaw graph.obj graph.slotted req.init req.goal
  let some kind := kind?.toKind? | return none
  return some { kind, str := expl, slotted := graph.slotted }
