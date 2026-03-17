import Lake
open Lake DSL

package CSQIT where
  version := "10.4.5"
  keywords := ["physics", "quantum", "gravity", "operad", "information"]
  homepage := "https://github.com/New-Beginning-Universe-Research-Group/CSQIT"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "v4.15.0"

@[default_target]
lean_lib CSQIT where
  globs := #[.submodules `CSQIT, .submodules `Appendices]

lean_lib Appendices where
  globs := #[.submodules `Appendices]