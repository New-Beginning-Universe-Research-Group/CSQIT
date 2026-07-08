/-
CSQIT v11.2.0 Lake 项目配置文件
版本: 11.2.0
Lean 版本: v4.29.0-rc6
日期: 2026-07-03

本文件定义了 CSQIT 项目的 Lake 构建配置，
包括 mathlib 依赖和 Core/Appendices 模块。
-/

import Lake
open Lake DSL

package csqit where
  version := v!"11.2.0"
  leanOptions := #[⟨`linter.unreachableTactic, false⟩, ⟨`linter.unusedTactic, false⟩]

require mathlib from "/mnt/d/2_ResearchProgram/Lean4/lean_deps/.lake/packages/mathlib"

@[default_target]
lean_lib CSQIT where
  roots := #[
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
    `Core.TwoAspectTheorems,
    `Core.HierarchicalWeaving,
    `Core.Hierarchy,
    `Core.HDST,
    `Core.Models.FiniteWeavingExamples,
    `Core.Models.PeriodicTable,
    `Core.Models.EnhancedModels,
    `Core.Models.FinModels,
    `FutureWork.Appendices.AppendixJ.ElectricPotential,
    `FutureWork.Appendices.AppendixK.NuclearFusionFission,
    `FutureWork.Appendices.AppendixL.PhysicsCorrespondence,
    `FutureWork.Appendices.AppendixM.Magnetism,
    `FutureWork.Appendices.AppendixN.ElectromagneticUnification,
    `FutureWork.Appendices.AppendixO.Conductivity,
    `FutureWork.Appendices.AppendixP.PhaseStates,
    `FutureWork.Appendices.AppendixQ.CrystalGrowth,
    `FutureWork.Appendices.AppendixR.Transparency,
    `FutureWork.Appendices.AppendixS.MatterEnergyUnification,
    `FutureWork.Appendices.AppendixT.GrandUnification,
    `FutureWork.Appendices.AppendixU.PhotoelectricRelation,
    `FutureWork.Appendices.AppendixV.PhiUnification,
    `FutureWork.Appendices.AppendixW.FineStructureConstant,
    `FutureWork.Appendices.AppendixX.LambdaCDM,
    `FutureWork.Appendices.AppendixY.HubbleConstant,
    `FutureWork.Appendices.AppendixZ.GravitationalConstant
  ]