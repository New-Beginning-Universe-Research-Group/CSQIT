/-
CSQIT v11.2.0 Lake 项目配置文件
版本: 11.2.0
Lean 版本: v4.29.0-rc6
日期: 2026-07-02

本文件定义了 CSQIT 项目的 Lake 构建配置，
包括 mathlib 依赖和 Core/Appendices 模块。
-/

import Lake
open Lake DSL

package csqit where
  version := v!"11.2.0"
  leanOptions := #[⟨`linter.unreachableTactic, false⟩, ⟨`linter.unusedTactic, false⟩]

-- mathlib 依赖（使用本地路径）
require mathlib from "/home/dell/lean_deps/.lake/packages/mathlib"

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
    `Core.Consistency
  ]
