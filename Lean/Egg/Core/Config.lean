namespace Egg.Config

structure Normalization where
  betaReduceRws := true
  etaReduceRws  := true
  natReduceRws  := true
  deriving BEq

def Normalization.noReduce : Normalization where
  betaReduceRws := false
  etaReduceRws  := false
  natReduceRws  := false

structure Encoding extends Normalization where
  eraseProofs   := true
  -- TODO: Erasure of types might not work as `isDefEq` expects expressions to be well-typed:
  --       https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Unify.20level.20mvars/near/416858547
  eraseLambdaDomains := false
  eraseForallDomains := false
  deriving BEq

structure Gen where
  genTcProjRws := true
  genTcSpecRws := true
  eagerTcSpec  := false
  genNatLitRws := true
  genEtaRw     := true
  genBetaRw    := true
  deriving BEq

structure Backend where
  blockInvalidMatches := true
  shiftCapturedBVars  := true -- This option implies `blockInvalidMatches`.
  optimizeExpl        := true
  timeLimit           := 10
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

structure _root_.Egg.Config extends Encoding, Gen, Backend, Debug

-- TODO: Why aren't these coercions automatic?

instance : Coe Encoding Normalization where
  coe := Encoding.toNormalization

instance : Coe Config Encoding where
  coe := toEncoding

instance : Coe Config Gen where
  coe := toGen
