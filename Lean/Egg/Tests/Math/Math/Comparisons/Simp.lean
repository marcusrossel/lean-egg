import Lean

initialize do pure () <* Lean.Meta.registerSimpAttr `bool_simp ""
initialize do pure () <* Lean.Meta.registerSimpAttr `lie_simp ""
initialize do pure () <* Lean.Meta.registerSimpAttr `rotman_simp ""
