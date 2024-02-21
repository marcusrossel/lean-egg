import Egg.Core.Request
import Lean
open Lean Elab Tactic

initialize registerTraceClass `egg
initialize registerTraceClass `egg.frontend (inherited := true)
initialize registerTraceClass `egg.reconstruction (inherited := true)

namespace Egg

-- TODO: Replace this with a `MessageData` instance.
def Request.trace (req : Request) : TacticM Unit := do
  withTraceNode `egg.frontend (fun _ => return "Request") do
    withTraceNode `egg.frontend (fun _ => return "Goal") (collapsed := false) do
      withTraceNode `egg.frontend (fun _ => return "LHS") do trace[egg.frontend] req.lhs
      withTraceNode `egg.frontend (fun _ => return "RHS") do trace[egg.frontend] req.rhs
    let rwsTitle := (if req.rws.isEmpty && !req.genNatLitRws then "No " else "") ++ "Rewrites"
    withTraceNode `egg.frontend (fun _ => return rwsTitle) (collapsed := false) do
      for rw in req.rws do
        withTraceNode `egg.frontend (fun _ => return m!"{rw.name}") do
          trace[egg.frontend] "Directions: {rw.dirs}"
          withTraceNode `egg.frontend (fun _ => return "LHS") (collapsed := false) do trace[egg.frontend] rw.lhs
          withTraceNode `egg.frontend (fun _ => return "RHS") (collapsed := false) do trace[egg.frontend] rw.rhs
      if req.genNatLitRws then trace[egg.frontend] "Nat Literal Conversions"
