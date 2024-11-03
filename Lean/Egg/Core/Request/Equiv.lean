import Egg.Core.Encode.Basic
import Egg.Core.Explanation.Basic
import Egg.Core.Request.EGraph
import Lean
open Lean

namespace Egg.Request

structure Equiv where
  init : Expression
  goal : Expression

def Equiv.encoding (init goal : Expr) (ctx : EncodingCtx) : MetaM Equiv :=
  return { init := ← encode init ctx, goal := ← encode goal ctx }

end Request

@[extern "explain_equiv"]
private opaque explainEquivRaw (graph : @& EGraph.Obj) (slotted : Bool) (e₁ e₂ : Expression) : String

def EGraph.run (graph : @& EGraph) (req : Request.Equiv) : Explanation.Raw where
  str := explainEquivRaw graph.obj graph.slotted req.init req.goal
  slotted := graph.slotted
