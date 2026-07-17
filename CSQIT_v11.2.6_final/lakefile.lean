/-
CSQIT — Lake 项目配置文件
版本: v11.6.0
Lean 版本: v4.29.0-rc6
日期: 2026-07-12

本文件定义了 CSQIT 项目的 Lake 构建配置，
包括 mathlib 依赖和各层级模块。

项目结构说明（按 W1/W2/W3 分级）：

W1 — 形式化数学核心（严格定义与证明）
  Core/W1/
    Axioms.lean              核心公理体系
    BasicModels.lean         基本模型（非平凡实例）
    FoundationalGrowth.lean  生长基础
    HierarchicalLevels.lean  层级结构定义
    AlgebraicCausality.lean  代数因果
    TwoAspectToSU2.lean      两面性到SU(2)
    CausalLattice.lean       因果格
    WeavingStructure.lean    编织结构 + ParallelWeave
    CausalWeaving.lean       因果编织
    AmplitudeTheorems.lean   振幅定理
    TwoAspectTheorems.lean   两面性定理
    HierarchicalWeaving.lean 层级编织
    Consistency.lean         一致性证明
    ShellCapacityDerivation.lean 壳层容量推导
    BasicProperties.lean     Eckmann-Hilton 严格定理
    ThreeGroupHierarchy.lean 三群谱系统一定义
    AxiomC_Independence.lean 公理独立性
    AxiomD_Independence.lean
    Independence.lean
    CausalLatticeToAxiomA.lean
    CausalSetCorrespondence.lean
    GrowthToAxioms.lean
    Hierarchy.lean
    Unified.lean
    Models/
      FinModels.lean         有限模型

W2 — 有效理论（应用模型与物理推导）
  Core/W2/
    ScaleDynamics.lean       尺度动力学
    B_V_Naturalness.lean     B/V自然性
    HDST.lean                高维时空
    ContinuumLimit.lean      连续极限
    Summary.lean             总结文档
    Integration.lean         v11+v12整合方案
    GrowthModel.lean         生长模型
    PhysicalConstants.lean   物理常数
    ThreeLocksDerivation.lean 三锁常数推导
    StrictDerivation.lean    严格推导
    GravityDerivation.lean   引力推导
    GroupRepresentationData.lean 群表示数据
    GrowthAndSymmetry.lean   生长与对称
    Models/
      EnhancedModels.lean    增强模型
      PeriodicTable.lean     元素周期表
      FiniteWeavingExamples.lean 有限编织示例

W3 — 探索性框架（概念性与实验性内容）
  Core/W3/
    Core.lean               核心公理体系（操作本体论）
    Models.lean             具体模型（操作本体论）
    AtomicOperations.lean   原子操作分类
    UnifiedPicture.lean     综合解析：统一图景
    CyclicUniverse.lean     循环宇宙：无始无终的群论图景
    Summary.lean            综合总结：生长的对称谱系

Unified/Constants/  三锁统一闭包（核心成果层，W1完成态）
Unified/Models/     应用物理模型（W2/W1应用态）
Appendices/         附录文档
papers/             相关论文
-/

import Lake
open Lake DSL

package csqit where
  version := v!"11.6.0"
  leanOptions := #[⟨`weak.linter.unreachableTactic, false⟩, ⟨`weak.linter.unusedTactic, false⟩]

require mathlib from "/home/dell/lean_deps/.lake/packages/mathlib"

@[default_target]
lean_lib CSQIT where
  roots := #[
    -- ===== W1：形式化数学核心 =====
    `Core.W1.Axioms,
    `Core.W1.BasicModels,
    `Core.W1.FoundationalGrowth,
    `Core.W1.HierarchicalLevels,
    `Core.W1.AlgebraicCausality,
    `Core.W1.TwoAspectToSU2,
    `Core.W1.CausalLattice,
    `Core.W1.WeavingStructure,
    `Core.W1.CausalWeaving,
    `Core.W1.AmplitudeTheorems,
    `Core.W1.TwoAspectTheorems,
    `Core.W1.HierarchicalWeaving,
    `Core.W1.Consistency,
    `Core.W1.ShellCapacityDerivation,
    `Core.W1.BasicProperties,
    `Core.W1.ThreeGroupHierarchy,
    `Core.W1.AxiomC_Independence,
    `Core.W1.AxiomD_Independence,
    `Core.W1.Independence,
    `Core.W1.CausalLatticeToAxiomA,
    `Core.W1.CausalSetCorrespondence,
    `Core.W1.GrowthToAxioms,
    `Core.W1.Hierarchy,
    `Core.W1.Unified,
    `Core.W1.Models.FinModels,
    -- ===== W2：有效理论 =====
    `Core.W2.ScaleDynamics,
    `Core.W2.B_V_Naturalness,
    `Core.W2.HDST,
    `Core.W2.ContinuumLimit,
    `Core.W2.Summary,
    `Core.W2.Integration,
    `Core.W2.GrowthModel,
    `Core.W2.PhysicalConstants,
    `Core.W2.ThreeLocksDerivation,
    `Core.W2.StrictDerivation,
    `Core.W2.GravityDerivation,
    `Core.W2.GroupRepresentationData,
    `Core.W2.GrowthAndSymmetry,
    `Core.W2.Fin7Uniqueness,
    `Core.W2.Models.EnhancedModels,
    `Core.W2.Models.PeriodicTable,
    `Core.W2.Models.FiniteWeavingExamples,
    -- ===== W3：探索性框架 =====
    `Core.W3.Core,
    `Core.W3.Models,
    `Core.W3.AtomicOperations,
    `Core.W3.UnifiedPicture,
    `Core.W3.CyclicUniverse,
    `Core.W3.Summary,
    -- ===== 三锁统一闭包（核心成果） =====
    `Unified.Constants.FineStructure,
    `Unified.Constants.LambdaCDM,
    `Unified.Constants.Hubble,
    `Unified.Constants.Gravity,
    `Unified.Constants.CrossConsistency,
    -- ===== 应用物理模型 =====
    `Unified.Models.Electrostatics,
    `Unified.Models.Magnetism,
    `Unified.Models.Conductivity,
    `Unified.Models.PhaseStates,
    `Unified.Models.Transparency
  ]