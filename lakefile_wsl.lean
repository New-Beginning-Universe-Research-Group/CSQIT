import Lake
open Lake DSL

package CSQIT where
  version := "10.4.5"
  keywords := ["physics", "quantum", "gravity", "operad", "information"]
  homepage := "https://github.com/New-Beginning-Universe-Research-Group/CSQIT"

require mathlib from "/home/user/.mathlib4/mathlib4-4.29.1"

@[default_target]
lean_lib CSQIT where
  globs := #[.submodules `CSQIT, .submodules `Appendices]

lean_lib Appendices where
  globs := #[.submodules `Appendices]