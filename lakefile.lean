import Lake
open Lake DSL

package csqit

require mathlib from "/home/dell/lean_deps/.lake/packages/mathlib"

@[default_target]
lean_lib CSQIT where
  roots := #[
    `Core.Axioms,
    `Core.CausalWeaving,
    `Core.AmplitudeTheorems,
    `Core.TwoAspectTheorems,
    `Core.Theorems,
    `Core.Models.FinModels,
    `Core.Models.EnhancedModels,
    `Core.WeavingStructure,
    `Core.HierarchicalWeaving,
    `Core.TradeoffAndVerification,
    `Core.Philosophy,
    `Core.HDST,
    `Core.Hierarchy,
    `Appendices.AppendixA.Uniqueness,
    `Appendices.AppendixB.CausalAndProbability,
    `Appendices.AppendixD.CausalStructure,
    `Appendices.AppendixJ.Mathematics
  ]