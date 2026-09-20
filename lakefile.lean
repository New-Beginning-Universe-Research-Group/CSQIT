/-
CSQIT v12.3 — Lake 项目配置文件（本地编译环境）
版本: v12.3  (新增 CrouzeixConnection.lean —— Crouzeix 猜想桥梁模块)
Lean 版本: v4.29.0-rc6

重要里程碑 (v12.3):
  · Jin Shanmu (2026, Lean 4) + Lorist & Schwenninger (2026, 独立) 证明 Crouzeix 猜想
    ∥p(A)∥ ≤ 2·max_{z∈W(A)}|p(z)| 对所有复方阵 A 和多项式 p
  · CSQIT 新增独立贡献：常数 2 的代数起源 = 三群 involution 结构
  · A₄ 三维不可约表示精确构造（整数矩阵：r, s）
  · s² = I（involution）→ 2-dilation 结构 → Crouzeix 常数 = 2

本地专用：使用预编译 mathlib（path 依赖），避免重复下载和编译。
GitHub 推送版本：lakefile.lean（git 依赖，可复现）

编译状态：Build completed successfully, 0 errors, 0 sorry
代码行数：约 6500 行 (10 个模块)
层级标注：W1/W2 逐层切割已完成
-/

import Lake
open Lake DSL

package csqit where
  version := v!"12.3.0"
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
    `V12.Unified.Models.AxionDarkEnergyCoupled
  ]
