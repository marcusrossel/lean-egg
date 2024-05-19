import Lake
open Lake DSL

package «rotman» where

@[default_target]
lean_lib Rotman where

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"
require egg from "../../../.."
