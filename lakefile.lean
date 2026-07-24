/-
CSQIT v12.0.0 — Lake 项目配置文件（纯 V12 终极编译器）
版本: v12.0.0
Lean 版本: v4.29.0-rc6
日期: 2026-07-24

本分支仅包含 V12 终极编译器模块，不含 Core/W1、Core/W2、Core/W3 等前版本代码。
V12 模块是自包含的，仅依赖 Mathlib。

模块结构：
  V12/Core/
    Foundation.lean             基础：公理体系、因果格、物理常数、射影尺度、扩展闭包序列
    AlgebraicTimeCircle.lean    代数时间之圆：TimeCircle S¹、能标生成函数、Λ_extended
    QuantumTimeCircle.lean      量子时间之圆：振幅-相位映射、贝里相位
    GravitationalAnomaly.lean   引力反常：编织曲率、曲率跳变、拓扑耗散
    CSQITWeaver.lean            CSQIT编织机网络：8节点共识、暗能量状态方程
    TopologicalTime.lean        拓扑时间：因果链涌现、时间圆极限
  V12/Unified/Models/
    AxionDarkEnergyCoupled.lean 轴子-暗能量耦合：四层作用量、预言验证报告

编译状态：Build completed successfully (2074 jobs), 0 errors, 0 sorry
第一性原理纯度：100% (零外部输入, 零观测拟合)
-/

import Lake
open Lake DSL

package csqit where
  version := v!"12.0.0"
  leanOptions := #[⟨`weak.linter.unreachableTactic, false⟩, ⟨`weak.linter.unusedTactic, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "6fc4d4f887"

@[default_target]
lean_lib CSQIT where
  roots := #[
    -- ===== V12：终极编译器模块（自包含，仅依赖 Mathlib） =====
    `V12.Core.Foundation,
    `V12.Core.AlgebraicTimeCircle,
    `V12.Core.QuantumTimeCircle,
    `V12.Core.GravitationalAnomaly,
    `V12.Core.CSQITWeaver,
    `V12.Core.TopologicalTime,
    `V12.Unified.Models.AxionDarkEnergyCoupled
  ]
