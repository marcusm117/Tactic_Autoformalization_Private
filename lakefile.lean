import Lake
open Lake DSL

package tacticFormalization where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.28.0"

require Canonical from git
  "https://github.com/chasenorman/CanonicalLean.git" @ "v4.28.0"

@[default_target]
lean_lib TacticFormalization
