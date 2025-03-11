import Egg.Tactic.Config.Option

namespace Egg

scoped macro "egg_no_defeq" : command => `(
  set_option egg.beta false
  set_option egg.eta false
  set_option egg.etaExpand false
  set_option egg.natLit false
  set_option egg.levels false
  set_option egg.structProj false
)
