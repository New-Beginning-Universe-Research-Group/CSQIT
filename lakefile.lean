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

require mathlib from "/mnt/d/2_ResearchProgram/Lean4/lean_deps/.lake/packages/mathlib"

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
    `Core.Models.FiniteWeavingExamples,
    `Core.Models.PeriodicTable,
    `Core.Models.EnhancedModels,
    `Core.Models.FinModels,
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
    `Unified.Models.Transparency,
    -- 探索性附录（W2/W3概念态）
    -- 注：以下模型已迁移至 Unified/Models/，旧文件保留在 FutureWork/ 仅作历史参考：
    --   AppendixJ/ElectricPotential → Unified.Models.Electrostatics
    --   AppendixM/Magnetism → Unified.Models.Magnetism
    --   AppendixO/Conductivity → Unified.Models.Conductivity
    --   AppendixP/PhaseStates → Unified.Models.PhaseStates
    --   AppendixR/Transparency → Unified.Models.Transparency（已删除）
    `FutureWork.Appendices.AppendixK.NuclearFusionFission,
    `FutureWork.Appendices.AppendixL.PhysicsCorrespondence,
    `FutureWork.Appendices.AppendixN.ElectromagneticUnification,
    `FutureWork.Appendices.AppendixQ.CrystalGrowth,
    `FutureWork.Appendices.AppendixS.MatterEnergyUnification,
    `FutureWork.Appendices.AppendixT.GrandUnification,
    `FutureWork.Appendices.AppendixU.PhotoelectricRelation,
    `FutureWork.Appendices.AppendixV.PhiUnification,
    `FutureWork.Appendices.AppendixW.FineStructureConstant,
    `FutureWork.Appendices.AppendixX.LambdaCDM,
    `FutureWork.Appendices.AppendixY.HubbleConstant,
    `FutureWork.Appendices.AppendixZ.GravitationalConstant
  ]