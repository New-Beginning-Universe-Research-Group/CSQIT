import Lake
open Lake DSL

package csqit where
  version := v!"10.4.5"

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc6"

lean_lib CSQIT where
  roots := #[
    `Core.Axioms,
    `Core.Theorems,
    `Core.Models.FinModels,
    `Core.Models.EnhancedModels,
    `Core.HDST,
    `Core.Consistency,
    `Core.Independence,
    `Core.AxiomD_Independence,
    `Core.AxiomC_Independence,
    `Core.WeavingStructure,
    `Core.Hierarchy,
    `Core.Unified,
    `Core.Summary,
    `Core.Philosophy,
    `Core.OpenProblems,
    `Core.README
  ]
