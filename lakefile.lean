import Lake
open Lake DSL

package CSQIT_W1 where
  version := v!"13.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "6fc4d4f887b81826d7e577d31ff43075f0833dc9"

/-! 第八轮任务 2：全量构建验收。

roots 已扩展到 CSQIT_W1/ 下的全部模块（31 个 .lean），包括此前
不在构建内的检验文件（IndependenceCheck、AxiomAudit、
CurvatureEnergyRefutation）与修复后的 GenerationBridge 墓碑、
TheoryFoundations（纯注释）。

排除项（不参与构建，原因见 BOUNDARIES §8）：
  · GenerationBridge_legacy.lean.disabled —— 原 GB 1948 行残骸，
    从未编译通过，扩展名非 .lean，Lake 不识别。 -/

@[default_target]
lean_lib CSQIT_W1 where
  roots := #[
    `CSQIT_W1.Foundation,
    `CSQIT_W1.GroupTheoreticOrigin,
    `CSQIT_W1.MinimalCost,
    `CSQIT_W1.AttractorPrototype,
    `CSQIT_W1.PhysicalPredictions,
    `CSQIT_W1.CompilerAxioms,
    `CSQIT_W1.CoreCollapse,
    `CSQIT_W1.AxiomIndependence,
    `CSQIT_W1.AxiomDerivation,
    `CSQIT_W1.QuantumCorrection,
    `CSQIT_W1.ObserverLayering,
    `CSQIT_W1.PhysicalConnect,
    `CSQIT_W1.WeaverPopulation,
    `CSQIT_W1.AlgebraicTimeCircle,
    `CSQIT_W1.GenerationBridge,
    `CSQIT_W1.TheoryFoundations,
    `CSQIT_W1.SequenceStructure,
    `CSQIT_W1.TwoAdicStructure,
    `CSQIT_W1.TopologicalTime,
    `CSQIT_W1.QuantumTimeCircle,
    `CSQIT_W1.TwoAspect,
    `CSQIT_W1.TwoAspectNoFinite,
    `CSQIT_W1.CrossConsistency,
    `CSQIT_W1.Declaration,
    `CSQIT_W1.AxionDarkEnergy,
    `CSQIT_W1.GravitationalAnomaly,
    `CSQIT_W1.CSQITWeaver,
    `CSQIT_W1.Main,
    `CSQIT_W1.IndependenceCheck,
    `CSQIT_W1.SolsAnyFamilies,
    `CSQIT_W1.CurvatureEnergyRefutation,
    `CSQIT_W1.AxiomAudit
  ]

/-! 增强公理体系（v11.2.8 全量移植）。
独立上层模块，与 CSQIT_W1 并存；不修改 CSQIT_W1 任何文件。 -/
@[default_target]
lean_lib CSQIT_Enhanced where
  roots := #[
    `CSQIT_Enhanced.Axioms,
    `CSQIT_Enhanced.EnhancedModels,
    `CSQIT_Enhanced.PeriodicTable,
    `CSQIT_Enhanced.Bridge,
    `CSQIT_Enhanced.AxiomAuditEnhanced,
    `CSQIT_Enhanced.EvolutionFaithfulness
  ]

/-! 第一代（V1.0 → V7.1.1）→ v23 接口检验。
独立目录；不改 CSQIT_W1 / CSQIT_Enhanced 任何文件；零新增 axiom、零 sorry。 -/
@[default_target]
lean_lib CSQIT_V1Bridge where
  roots := #[
    `CSQIT_V1Bridge.OrderAndFixedPoint,
    `CSQIT_V1Bridge.OrderAndAction,
    `CSQIT_V1Bridge.CausalAmplitudeLayer,
    `CSQIT_V1Bridge.CausalLayerSharpening,
    `CSQIT_V1Bridge.LayerWitness,
    `CSQIT_V1Bridge.StructuralLimits,
    `CSQIT_V1Bridge.CausalSetWitness,
    `CSQIT_V1Bridge.NonTotalModel,
    `CSQIT_V1Bridge.PowerStructure,
    `CSQIT_V1Bridge.GaugeAndEndo,
    `CSQIT_V1Bridge.OperadImpossibility,
    `CSQIT_V1Bridge.AxiomCClassification,
    `CSQIT_V1Bridge.ColoredOperadNoGo,
    `CSQIT_V1Bridge.GeneralModelClassification,
    `CSQIT_V1Bridge.OrderRigidity,
    `CSQIT_V1Bridge.FiniteSeparation,
    `CSQIT_V1Bridge.OrderUniqueness,
    `CSQIT_V1Bridge.AmplitudeStructure,
    `CSQIT_V1Bridge.LayerIndependence,
    `CSQIT_V1Bridge.AmplitudeRigidity,
    `CSQIT_V1Bridge.AxiomCRigidity,
    `CSQIT_V1Bridge.FreeModel,
    `CSQIT_V1Bridge.V23Interface,
    `CSQIT_V1Bridge.OrderMaximality
  ]

/-! 分层 AxiomC 塔（设计候选）。
独立目录；不改 CSQIT_W1 / CSQIT_Enhanced / CSQIT_V1Bridge 任何文件；
零新增 axiom、零 sorry。 -/
@[default_target]
lean_lib CSQIT_LayerTower where
  roots := #[
    `CSQIT_LayerTower.Tower,
    `CSQIT_LayerTower.Top,
    `CSQIT_LayerTower.AxiomCMaximality,
    `CSQIT_LayerTower.Potential
  ]

/-! 层级切口探索（第 25 轮）。
独立目录；不改 CSQIT_W1 / CSQIT_Enhanced / CSQIT_V1Bridge 任何文件；
零新增 axiom、零 sorry。仅落地已能证的部分。 -/
@[default_target]
lean_lib CSQIT_LayerCuts where
  roots := #[
    `CSQIT_LayerCuts.Cuts
  ]

/-! 振幅结构定理桥（第二十六轮）：G38/G39 的结构化。
独立目录；不改 CSQIT_W1 / CSQIT_Enhanced / CSQIT_V1Bridge 任何文件；
零新增 axiom、零 sorry。 -/
@[default_target]
lean_lib CSQIT_Bridge where
  roots := #[
    `CSQIT_Bridge.AmplitudeSemigroup
  ]

/-! 编织路径桥（第二十七轮）：v11.2.8 `structure Weave` 的独立重建与判定。
独立目录；不改 CSQIT_W1 / CSQIT_Enhanced / CSQIT_V1Bridge /
CSQIT_LayerTower / CSQIT_LayerCuts 任何文件；零新增 axiom、零 sorry。 -/
@[default_target]
lean_lib CSQIT_WeaveBridge where
  roots := #[
    `CSQIT_WeaveBridge.WeaveCore,
    `CSQIT_WeaveBridge.Independence
  ]

/-! 时间尺度判定（第 28 轮）：时间是尺度还是维度 + 螺旋 S¹ × ℝ_{>0}。
独立目录；不改 CSQIT_W1 / CSQIT_Enhanced / CSQIT_V1Bridge /
CSQIT_LayerTower / CSQIT_LayerCuts / CSQIT_WeaveBridge 任何文件；
零新增 axiom、零 sorry。 -/
@[default_target]
lean_lib CSQIT_TimeScale where
  roots := #[
    `CSQIT_TimeScale.Scale,
    `CSQIT_TimeScale.Spiral,
    `CSQIT_TimeScale.Verdict,
    `CSQIT_TimeScale.GapScale,
    `CSQIT_TimeScale.MulIndex,
    `CSQIT_TimeScale.PowerLaw,
    `CSQIT_TimeScale.Flow
  ]
