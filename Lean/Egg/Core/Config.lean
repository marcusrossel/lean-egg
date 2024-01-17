namespace Egg

inductive Config.TypeTags
  | none
  | indices
  | exprs
  deriving BEq

-- TODO: Add a configuration option that reduces terms. This is useful for debugging.
--
-- TODO: At some point it might be a good idea to split this into multiple kinds of configs which
--       extend eachother. For example, the first three properties could be an encoding config.
--       The `optimizeExpl` and `dbgBypass` properties aren't relevant for that.
--
-- TODO: Make `eraseProofs` and `eraseULvls` true by default once proof reconstruction can support
--       it.
structure Config where
  eraseProofs  := false
  eraseULvls   := false
  typeTags     := Config.TypeTags.none
  optimizeExpl := false
  buildProof   := true
  dbgBypass    := false
