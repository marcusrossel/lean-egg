namespace Egg.Config

structure Encoding where
  betaReduceRws := true
  etaReduceRws  := true
  eraseProofs   := true
  -- TODO: Erasure of types might not work as `isDefEq` expects expressions to be well-typed:
  --       https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Unify.20level.20mvars/near/416858547
  eraseLambdaDomains := false
  eraseForallDomains := false
  deriving BEq

structure Gen where
  genTcProjRws := true
  genTcSpecRws := true
  genNatLitRws := true
  genEtaRw     := true
  genBetaRw    := true
  deriving BEq

structure Backend where
  blockInvalidMatches := true
  shiftCapturedBVars  := true -- This option implies `blockInvalidMatches`.
  optimizeExpl        := true
  deriving BEq

inductive Debug.ExitPoint
  | none
  | beforeEqSat
  | beforeProof
  deriving BEq, Inhabited

structure Debug where
  exitPoint           := Debug.ExitPoint.none
  vizPath             := (none : Option String)
  -- TODO: Debug tracing is currently disabled in Rust as it breaks builds on Linux.
  traceSubstitutions  := false
  traceBVarCorrection := false
  deriving BEq

end Config
open Config

structure Config extends Encoding, Gen, Backend, Debug
