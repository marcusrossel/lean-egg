
import Egg.Core.Encode.Basic
import Egg.Core.Explanation.Basic
import Egg.Core.Request.Basic
import Egg.Core.Request.EGraph
import Lean
open Lean

namespace Egg

def parse (s : String) (eagerSynth := false) : MetaM Expr := do
  match Parser.runParserCategory (← getEnv) `egg_expr s with
  | .ok stx    =>
    let a := Explanation.parseExpr ⟨ stx ⟩
    match a with
      | .error _ => throwError "not ok"
      | .ok (c, _) => c.toExpr (synthesize := eagerSynth)
  | .error _ => throwError "meh"

structure Request.Term where
  enode : Nat

@[extern "get_term"]
private opaque getTermRaw (graph : EGraph.Obj) (slotted : Bool) (enode : Nat) : String

def EGraph.get (graph : EGraph) (req : Request.Term) : MetaM Expr := do
  parse <| getTermRaw graph.obj graph.slotted req.enode
