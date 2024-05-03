import Egg.Core.Encode.Basic
import Egg.Core.Explanation.Basic
import Egg.Core.Request.EGraph
import Lean
open Lean

namespace Egg.Request

structure Equiv where
  init : Expression
  goal : Expression

def Equiv.encoding (init goal : Expr) (cfg : Egg.Config) (amb : MVars.Ambient) : MetaM Equiv :=
  return { init := ← encode init cfg amb, goal := ← encode goal cfg amb }

end Request

@[extern "explain_equiv"]
private opaque explainEquivRaw (graph : @& EGraph) (e₁ e₂ : Expression) : Explanation.Raw

def EGraph.run (graph : @& EGraph) (req : Request.Equiv) : Explanation.Raw :=
  explainEquivRaw graph req.init req.goal
