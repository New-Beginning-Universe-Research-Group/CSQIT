import Lake
open Lake DSL

package csqit where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

require mathlib from "/home/dell/lean_deps/.lake/packages/mathlib"

@[default_target]
lean_lib CSQIT where
  roots := #[
    `Core.Axioms,
    `Core.Theorems,
    `Core.Consistency,
    `Core.Independence,
    `Core.AxiomD_Independence,
    `Core.AxiomC_Independence,
    `Core.CausalWeaving,
    `Core.AlgebraicCausality,
    `Core.WeavingStructure,
    `Core.AmplitudeTheorems,
    `Core.TwoAspectTheorems,
    `Core.HierarchicalWeaving,
    `Core.HierarchicalLevels,
    `Core.Hierarchy,
    `Core.TradeoffAndVerification,
    `Core.FoundationalGrowth,
    `Core.GrowthToAxioms,
    `Core.TwoAspectToSU2,
    `Core.CompleteHierarchicalCascade,
    `Core.UnifiedLivingParadigm,
    `Core.ShellCapacityDerivation,
    `Core.ComputationalPillars,
    `Core.HDST,
    `Core.Unified,
    `Core.Philosophy,
    `Core.Summary,
    `Core.OpenProblems,
    `Core.CausalLattice,
    `Core.QuantumMeasurement,
    `Core.ThermodynamicArrow,
    `Core.DarkUniverse,
    `Core.CausalSetCorrespondence,
    `Core.B_V_Naturalness,
    `Core.CausalLatticeToAxiomA,
    `Core.BasicModels,
    `Core.Models.FinModels,
    `Core.Models.EnhancedModels,
    `Core.Models.Fin8Growth,
    `Core.Models.TwoAspectBalancedVerification,
    `Core.Models.FiniteWeavingExamples,
    `Core.Models.SmallSemigroupExploration,
    `Core.Models.PeriodicTable,
    `Appendices.AppendixA.Uniqueness,
    `Appendices.AppendixB.CausalAndProbability,
    `Appendices.AppendixC.CausalStructure,
    `Appendices.AppendixD.BlackHoleThermo,
    `Appendices.AppendixE.Mathematics
  ]