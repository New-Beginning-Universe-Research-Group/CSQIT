# CSQIT Lean4 编译环境配置 (已锁定 v1.2)

## 🛠️ 工具链版本
- **Lean 版本**: `leanprover/lean4:v4.29.0-rc6` ⚠️ **发布候选版**
- **工具链路径**: `/root/.elan/toolchains/leanprover--lean4---v4.29.0-rc6/bin/lean`
- **Lake 二进制**: `/root/.elan/toolchains/leanprover--lean4---v4.29.0-rc6/bin/lake`
- **工具链配置**: `lean-toolchain` 文件中指定

## ⚠️ Lean RC 版使用说明

**为什么使用 RC 版？**
- 为匹配 WSL 环境中预编译的 mathlib 缓存
- 避免从源码重新编译 mathlib（耗时数小时）

**潜在风险：**
- RC 版可能从 Docker Hub 移除，建议尽快迁移到稳定版 v4.29.0
- Mathlib 版本已通过 `lakefile.lean` 中的 commit hash 锁定

**迁移到稳定版步骤：**
1. 更新 `lean-toolchain` 为 `leanprover/lean4:v4.29.0`
2. 更新 `lakefile.lean` 中的 mathlib commit
3. 重新编译 mathlib（首次需要数小时）
4. 验证所有模块编译通过

## 📦 Mathlib 依赖库
- **主路径**: `/home/dell/lean_deps/.lake/packages/mathlib`
- **备用路径**: `/root/.mathlib4/mathlib4/mathlib4-4.29.1`
- **版本**: 锁定 commit `7e9bc6aa06e01ff3fdfa28d45cfe7664c2d93f6`
- **状态**: ✅ 已预编译，版本已锁定

## 📁 项目文件结构
```
feat-csqit-lean4-formal-proof-vf7wFF/
├── Core/
│   ├── Models/
│   │   ├── FinModels.lean           (标准 Theory 模型)
│   │   └── EnhancedModels.lean      (Theory' + PartialTheory' 模型)
│   ├── Axioms.lean                  (核心公理: AxiomA-J, Theory)
│   ├── Theorems.lean                (核心定理 ~1500 行，含子主题索引)
│   ├── Consistency.lean             (一致性验证)
│   ├── Independence.lean            (独立性证明)
│   ├── OpenProblems.lean            (13 个开放问题)
│   └── ...
├── Appendices/                      (附录 A-O, 28 个文件)
├── FutureWork/                      (未来工作)
├── lakefile.lean                    (构建配置，Mathlib 版本已锁定)
├── lean-toolchain                   (v4.29.0-rc6)
└── COMPILATION_ENVIRONMENT.md       (本文件)
```

## 🚀 编译命令

### 方案 1: 使用 elan run
```bash
cd /mnt/c/Users/DELL/.trae-cn/worktrees/CSQIT-workspace/feat-csqit-lean4-formal-proof-vf7wFF
elan run leanprover/lean4:v4.29.0-rc6 -- lake build
```

### 方案 2: 直接使用工具链二进制
```bash
export LAKE=/root/.elan/toolchains/leanprover--lean4---v4.29.0-rc6/bin/lake
export LEAN=/root/.elan/toolchains/leanprover--lean4---v4.29.0-rc6/bin/lean
cd /mnt/c/Users/DELL/.trae-cn/worktrees/CSQIT-workspace/feat-csqit-lean4-formal-proof-vf7wFF
$LAKE build
```

### 方案 3: 逐步构建（推荐用于调试）
```bash
# 先构建 Core.Types
elan run leanprover/lean4:v4.29.0-rc6 -- lake build CSQIT.Core.Types

# 再构建 Core.Axioms
elan run leanprover/lean4:v4.29.0-rc6 -- lake build CSQIT.Core.Axioms

# 完整构建
elan run leanprover/lean4:v4.29.0-rc6 -- lake build
```

## 📚 关键 Mathlib 导入路径

| 功能 | 正确导入路径 | 注意事项 |
|------|-------------|---------|
| 集合有限性 | `Mathlib.Data.Set.Finite.Basic` | ❌ 不要用 `Mathlib.Data.Set.Finite` |
| 偏序关系 | `Mathlib.Order.Basic` | ❌ 不要用 `Mathlib.Order.Poset` |
| 复数绝对值 | `Mathlib.Data.Complex.Basic` | 或 `Mathlib.Data.Complex.Abs` |
| 拓扑收敛 | `Mathlib.Topology.Defs.Filter` | 用于 `Tendsto` |
| 可数性 | `Mathlib.Data.Countable.Defs` 或包含在基础导入中 | 通过 `Countable` 类型类 |
| 列表基础 | `Mathlib.Data.List.Basic` | ❌ 不要用 `Mathlib.Data.List.Defs` |

## ✅ 已修复的关键问题

1. **导入路径修复**
   - `Mathlib.Data.Set.Finite` → `Mathlib.Data.Set.Finite.Basic`
   - `Mathlib.Order.Poset` → `Mathlib.Order.Basic`
   - `Mathlib.Data.List.Defs` → `Mathlib.Data.List.Basic`

2. **公理系统结构**
   - `AxiomA`: 关系元集合 + 组合规则
   - `AxiomB`: 因果序 + 编织公理
   - `AxiomC`: 振幅函数 + 单射性（统一结构）
   - `AxiomD`-`AxiomI`: 其他公理化定义
   - `CSQIT`: 完整理论组合

3. **结构设计简化**
   - 移除了 `AmplitudeInjectivity` 独立结构，将其字段直接合并到 `AxiomC`
   - 简化了 `AxiomF` 中的连续极限表述
   - 修正了 `AxiomI` 中的 `A.C.connected` 引用

## 🔒 锁定声明

**重要**: 以下内容**严禁修改**，除非先完整备份当前状态：

1. ❌ `lean-toolchain` 版本：保持 `v4.29.0-rc6`
2. ❌ `lakefile.lean` 中 mathlib 路径
3. ❌ `/home/dell/lean_deps/` 下的预编译依赖库
4. ❌ `/root/.mathlib4/` 下的 mathlib4 库
5. ❌ `/root/.elan/toolchains/` 中的工具链文件

## 🚨 如需更改

1. 先完整备份当前项目
2. 先备份依赖库路径
3. 测试新配置在独立目录下是否可行
4. **不要直接修改生产环境**

## 📖 编译状态跟踪

| 模块 | 状态 | 备注 |
|-----|------|------|
| Core.Axioms | ✅ Ready | 核心公理定义 |
| Core.Models.FinModels | ✅ Ready | 标准 Theory 模型 |
| Core.Models.EnhancedModels | ✅ Ready | Theory' + PartialTheory' |
| Core.Theorems | ✅ Ready | 核心定理（含子主题索引）|
| Core.Independence | ✅ Ready | 独立性证明 |
| Core.OpenProblems | ✅ Ready | 13 个开放问题 |
| Appendices.* | ✅ Ready | 附录 A-O (28 文件) |
| FutureWork.* | ✅ Ready | 未来工作 (7 文件) |
