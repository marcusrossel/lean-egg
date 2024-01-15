namespace Egg

inductive Config.TypeTags
  | none
  | indices
  | exprs
  deriving BEq

-- TODO: At some point it might be a good idea to split this into multiple kinds of configs which
--       extend eachother. For example, the first three properties could be an encoding config.
--       The `dbgBypass` property isn't relevant for that.
structure Config where
  eraseProofs  := true
  eraseULvls   := true
  typeTags     := Config.TypeTags.none
  optimizeExpl := false
  dbgBypass    := false
