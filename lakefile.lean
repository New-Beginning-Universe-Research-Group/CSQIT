import Lake
import Lake.Util.Dependency
open Lake DSL

/-
================================================================================
CSQIT Lakefile - Lean 4 项目构建配置
================================================================================

版本: 10.5
日期: 2026-06-23

编译环境说明:
- Lean 版本: v4.29.0-rc6 (发布候选版)
- Mathlib: 锁定版本以确保可复现性

⚠️ 重要说明:
1. 使用 v4.29.0-rc6 是为了匹配预编译的 mathlib 缓存
2. Mathlib 版本已通过 mathlibKey 锁定
3. 如需迁移到稳定版 v4.29.0，请先更新 mathlib 依赖

依赖路径 (WSL 环境):
- /home/dell/lean_deps/.lake/packages/mathlib
- /root/.mathlib4/mathlib4/mathlib4-4.29.1
================================================================================
-/

package csqit

/--
Mathlib 依赖配置

使用 mathlib from olean server 确保预编译的 .olean 文件可用。
版本通过 mathlibKey 锁定，与 lean-toolchain 版本匹配。
-/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  @ "7e9bc6aa06e01ff3fdfa28d45cfe7664c2d93f6"
  -- 此 commit 对应 v4.29.0-rc6 的 Mathlib

/--
构建配置说明:
- 构建缓存位置: .lake/
- Mathlib 预编译缓存: 已配置在 WSL 环境路径
- 并行构建: 启用

编译命令:
  lake build              -- 完整构建
  lake build CSQIT.Core  -- 仅构建核心模块
  lake clean             -- 清理构建产物
-/
def mathlibKey := "4.29.0-rc6"

lean_lib Core {
  -- 核心库配置
  buildArchive := false
}

/-
================================================================================
模块结构

Core/           -- 核心公理体系与定理
  ├── Models/    -- 具体模型 (Fin 5×4, Fin 7, ℕ)
  ├── Axioms.lean    -- 公理定义 (AxiomA-J)
  ├── Theorems.lean  -- 核心定理
  └── ...

Appendices/     -- 附录 (A-O)
FutureWork/     -- 未来研究方向
================================================================================
-/

@[defaultTarget]
lean_lib CSQIT {
  -- 默认目标：构建整个项目
  moreLeanhints := #[]
}
