import Lake
open Lake DSL

package «four-frontiers-boundary-markers» where
  version := v!"0.1.0"

@[default_target]
lean_lib Fourfrontiers where
  globs := #[.submodules `Fourfrontiers]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
