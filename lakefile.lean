/-
CSQIT v11.2.6 Lake 项目配置文件
版本: 11.2.6
Lean 版本: v4.29.0-rc6
日期: 2026-07-09

本文件定义了 CSQIT 项目的 Lake 构建配置，
包括 mathlib 依赖和各层级模块。

模块层级说明：
- Core/              : 公理与硬核W1（基础层）
- Unified/Constants/ : 三锁统一闭包（核心成果层，W1完成态）
- Unified/Models/    : 应用物理模型（W2/W1应用态）
- FutureWork/        : 探索性存根（W2/W3概念态）

清理记录（v11.2.4）：
- 已移除已迁移到 Unified/Models/ 的旧 FutureWork 附录条目：
  * FutureWork.Appendices.AppendixJ.ElectricPotential → Unified.Models.Electrostatics
  * FutureWork.Appendices.AppendixM.Magnetism → Unified.Models.Magnetism
  * FutureWork.Appendices.AppendixO.Conductivity → Unified.Models.Conductivity
  * FutureWork.Appendices.AppendixP.PhaseStates → Unified.Models.PhaseStates
  * FutureWork.Appendices.AppendixR.Transparency → Unified.Models.Transparency（已删除）
-/

import Lake
open Lake DSL

package csqit where
  version := v!"11.2.6"
  leanOptions := #[⟨`linter.unreachableTactic, false⟩, ⟨`linter.unusedTactic, false⟩]

require mathlib from "/home/dell/lean_deps/.lake/packages/mathlib"

@[default_target]
lean_lib CSQIT where
  roots := #[
    -- 核心公理层（W1）
    `Core.Axioms,
    `Core.BasicModels,
    `Core.FoundationalGrowth,
    `Core.HierarchicalLevels,
    `Core.AlgebraicCausality,
    `Core.TwoAspectToSU2,
    `Core.CausalLattice,
    `Core.B_V_Naturalness,
    `Core.ShellCapacityDerivation,
    `Core.ScaleDynamics,
    `Core.Unified,
    `Core.Consistency,
    `Core.Theorems,
    `Core.CausalWeaving,
    `Core.AmplitudeTheorems,
    `Core.WeavingStructure,
    `Core.TwoAspectTheorems,
    `Core.HierarchicalWeaving,
    `Core.Hierarchy,
    `Core.HDST,
    `Core.ContinuumLimit,
    `Core.Models.FiniteWeavingExamples,
    `Core.Models.PeriodicTable,
    `Core.Models.EnhancedModels,
    `Core.Models.FinModels,
    -- v11.5 综合实验层（v11 本体 + v12 视角）
    `Core.v115.Integration,
    `Core.v115.GroupRepresentationData,
    `Core.v115.CyclicUniverse,
    `Core.v115.ThreeLocksDerivation,
    `Core.v115.ThreeGroupHierarchy,
    `Core.v115.GrowthAndSymmetry,
    `Core.v115.Summary,
    `Core.v115.StrictDerivation,
    `Core.v115.GravityDerivation,
    `Core.v115.GrowthModel,
    `Core.v115.PhysicalConstants,
    -- v12 实验性新公理体系（操作本体论）
    `Core.v12.Core,
    `Core.v12.Models,
    `Core.v12.AtomicOperations,
    `Core.v12.UnifiedPicture,
    `Core.v12.BasicProperties,
    -- 三锁统一闭包（核心成果，W1完成态）
    `Unified.Constants.FineStructure,
    `Unified.Constants.LambdaCDM,
    `Unified.Constants.Hubble,
    `Unified.Constants.Gravity,
    `Unified.Constants.CrossConsistency,
    -- 应用物理模型（W2/W1应用态）
    `Unified.Models.Electrostatics,
    `Unified.Models.Magnetism,
    `Unified.Models.Conductivity,
    `Unified.Models.PhaseStates,
    `Unified.Models.Transparency
  ]