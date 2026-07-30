/-
CSQIT v12.1.2 — Lake 项目配置文件（本地编译环境）
版本: v12.1.2
Lean 版本: v4.29.0-rc6

本地专用：使用预编译 mathlib（path 依赖），避免重复下载和编译。
GitHub 推送版本：lakefile.lean（git 依赖，可复现）

使用方法：
  cp lakefile.local.lean lakefile.lean
  或者在 lakefile.lean 中切换 require 方式

模块依赖顺序：
  Foundation.lean           (基础，无依赖)
    ↓
  AxiomDerivation.lean      (依赖 Foundation)
    ↓
  AlgebraicTimeCircle.lean  (依赖 Foundation)
    ↓
  QuantumTimeCircle.lean    (依赖 Foundation, AlgebraicTimeCircle)
    ↓
  GravitationalAnomaly.lean (依赖 Foundation, AlgebraicTimeCircle)
    ↓
  CSQITWeaver.lean          (依赖 Foundation, AlgebraicTimeCircle, QuantumTimeCircle, GravitationalAnomaly)
    ↓
  TopologicalTime.lean      (依赖 Foundation, AlgebraicTimeCircle, CSQITWeaver)
    ↓
  Fin7Uniqueness.lean       (自包含，仅依赖 Mathlib；W2 层 Fin 7 唯一性定理)
    ↓
  AxionDarkEnergyCoupled.lean (依赖所有上述模块)

编译状态：Build completed successfully, 0 errors, 0 sorry
代码行数：约 6220 行 (9 个模块)
层级标注（v12.1.2 诚实修正）：
  核心结构因子（420, k=5, 2π, c(n), 量子纠缠）= W1 严格
  α⁻¹ 表达式组合方式、B 构造、量级匹配 = W2 条件性
  Fin 7 唯一性定理 = W2 条件性（W1 严格定理 + W2 经验窗口）
AxiomD：W1 严格定理；AxiomI/J：W2 条件性（诚实标注）
-/

import Lake
open Lake DSL

package csqit where
  version := v!"12.1.2"
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
    `V12.Unified.Models.AxionDarkEnergyCoupled
  ]
