import Lean

initialize Lean.registerTraceClass `egg
initialize Lean.registerTraceClass `egg.frontend (inherited := true)
initialize Lean.registerTraceClass `egg.reconstruction (inherited := true)
