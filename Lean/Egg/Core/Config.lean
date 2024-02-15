namespace Egg

inductive Config.TypeTags
  | none
  | indices
  | exprs
  deriving BEq

inductive Config.ExitPoint
  | none
  | beforeEqSat
  | beforeProof
  deriving BEq

-- TODO: At some point it might be a good idea to split this into multiple kinds of configs which
--       extend eachother. For example, the first three properties could be an encoding config.
--       The `optimizeExpl` and `exitPoint` properties aren't relevant for that.
--
-- TODO: Make `eraseProofs` and `eraseULvls` true by default once proof reconstruction can support
--       it.
structure Config where
  eraseProofs  := false
  eraseULvls   := false
  genTcProjRws := true
  genNatLitRws := true
  typeTags     := Config.TypeTags.none
  reduce       := false
  optimizeExpl := false
  exitPoint    := Config.ExitPoint.none
