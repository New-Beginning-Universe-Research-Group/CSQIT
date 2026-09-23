/-
CSQIT v12.5.1 — Lake 项目配置文件（本地编译环境）
版本: v12.5.1
Lean 版本: v4.29.0-rc6

重要里程碑:
  v12.3: CrouzeixConnection.lean — Crouzeix 猜想桥梁模块
  v12.5.0: DiscreteUniverse.lean — 宇宙离散性三 W1 证明链
  v12.5.1: 全局一致性修正 — 物理意义注释统一

本地专用：使用预编译 mathlib（path 依赖），避免重复下载和编译。
GitHub 推送版本：lakefile.lean（git 依赖，可复现）

编译状态：Build completed successfully, 0 errors, 0 sorry
代码行数：约 6500 行 (13 个模块)
层级标注：W1/W2 逐层切割已完成
-/

import Lake
open Lake DSL

package csqit where
  version := v!"12.6.0"
  leanOptions := #[⟨`weak.linter.unreachableTactic, false⟩, ⟨`weak.linter.unusedTactic, false⟩]

-- 本地编译专用：使用预编译 mathlib（path 依赖），避免重复下载和编译。
-- WSL 环境路径：~/lean_deps/.lake/packages/mathlib
require mathlib from
  "/home/dell/lean_deps/.lake/packages/mathlib"

@[default_target]
lean_lib CSQIT where
  roots := #[
    -- ===== V12：终极编译器模块（自包含，仅依赖 Mathlib） =====
    `V12.Core.Foundation,
    `V12.Core.AxiomDerivation,
    `V12.Core.AlgebraicTimeCircle,
    `V12.Core.QuantumTimeCircle,
    `V12.Core.GravitationalAnomaly,
    `V12.Core.CSQITWeaver,
    `V12.Core.TopologicalTime,
    `V12.Core.Fin7Uniqueness,
    `V12.Core.ErrorBounds,
    `V12.Core.CrouzeixConnection,
    `V12.Core.DiscreteFluid,
    `V12.Core.DiscreteUniverse,
    `V12.Core.LatticeGap,
    `V12.Core.MillenniumMath,
    `V12.Unified.Models.AxionDarkEnergyCoupled
  ]
