import Lake
open Lake DSL

package «formal_ramsey» {
  -- add any package configuration options here
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"v4.2.0"

require proofwidgets from git "https://github.com/EdAyers/ProofWidgets4"@"v0.0.22"

@[default_target]
lean_lib «FormalRamsey» {
  -- add any library configuration options here
}
