import Lake
open Lake DSL

package CSQIT_W1 where
  version := v!"13.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "6fc4d4f887"

@[default_target]
lean_lib CSQIT_W1 where
  roots := #[
    `CSQIT_W1.Foundation,
    `CSQIT_W1.CoreCollapse,
    `CSQIT_W1.TwoAspect,
    `CSQIT_W1.TwoAspectNoFinite,
    `CSQIT_W1.AxiomDerivation,
    `CSQIT_W1.AlgebraicTimeCircle,
    `CSQIT_W1.QuantumTimeCircle,
    `CSQIT_W1.GravitationalAnomaly,
    `CSQIT_W1.CSQITWeaver,
    `CSQIT_W1.AxionDarkEnergy,
    `CSQIT_W1.PhysicalConnect,
    `CSQIT_W1.Main,
    `CSQIT_W1.CompilerAxioms,
    `CSQIT_W1.MinimalCost,
    `CSQIT_W1.AxiomIndependence,
    `CSQIT_W1.CrossConsistency,
    `CSQIT_W1.TwoAdicStructure,
    `CSQIT_W1.WeaverPopulation,
    `CSQIT_W1.SequenceStructure,
    -- CSQIT_W1.PhysicalPredictions, -- 暂时移除 (4.29 兼容性待修)
    -- CSQIT_W1.ObserverLayering,  -- 暂时移除 (4.29 兼容性待修)
    `CSQIT_W1.QuantumCorrection,
    -- CSQIT_W1.GenerationBridge,  -- 暂时移除 (4.29 兼容性待修)
    -- CSQIT_W1.AttractorPrototype, -- 暂时移除 (4.29 兼容性待修)
    -- CSQIT_W1.GroupTheoreticOrigin -- 暂时移除 (4.29 兼容性待修)
  ]