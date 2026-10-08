import Lake
open Lake DSL

package CSQIT_W1 where
  version := v!"13.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "6fc4d4f887b81826d7e577d31ff43075f0833dc9"

@[default_target]
lean_lib CSQIT_W1 where
  roots := #[
    `CSQIT_W1.Foundation,
    `CSQIT_W1.GroupTheoreticOrigin
  ]