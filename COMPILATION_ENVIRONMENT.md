# CSQIT Lean4 编译环境配置 (已锁定 v1.1)

## 🛠️ 工具链版本
- **Lean 版本**: `leanprover/lean4:v4.29.0-rc6`
- **工具链路径**: `/root/.elan/toolchains/leanprover--lean4---v4.29.0-rc6/bin/lean`
- **Lake 二进制**: `/root/.elan/toolchains/leanprover--lean4---v4.29.0-rc6/bin/lake`
- **工具链配置**: `lean-toolchain` 文件中指定

## 📦 Mathlib 依赖库
- **主路径**: `/home/dell/lean_deps/.lake/packages/mathlib`
- **备用路径**: `/root/.mathlib4/mathlib4/mathlib4-4.29.1`
- **版本**: 匹配 v4.29.0-rc6
- **状态**: ✅ 已预编译，无需下载

## 📁 项目文件结构
```
feat-csqit-lean4-formal-proof-vf7wFF/
├── Core/
│   ├── Types.lean          (RelationElement, BasicRule, 基础类型)
│   ├── Axioms.lean         (核心公理: AxiomA-I, CSQIT 完整结构)
│   ├── Base.lean           (基础定义和定理)
│   ├── Consistency.lean    (一致性验证)
│   ├── Hierarchy.lean      (层次结构)
│   ├── Operad.lean         (Operad 结构)
│   ├── Summary.lean        (总结)
│   ├── Theorems.lean       (定理)
│   └── Unified.lean        (统一理论)
├── Theorems/
│   ├── Associativity.lean  (结合性定理)
│   ├── Continuum.lean      (连续极限定理)
│   └── Cosmology.lean      (宇宙学定理)
├── Appendices/             (附录 A-O)
├── lakefile.lean           (已锁定的构建配置)
├── lean-toolchain          (v4.29.0-rc6)
└── COMPILATION_ENVIRONMENT.md (本文件)
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
| Core.Types | ✅ Ready | 基础类型定义 |
| Core.Axioms | ✅ Ready | 核心公理定义 |
| Core.Base | ⏳ 待验证 | 需 Core 模块通过 |
| Core.* | ⏳ 待验证 | 需先验证基础模块 |
| Theorems.* | ⏳ 待验证 | 需先验证 Core |
| Appendices.* | ⏳ 待验证 | 需先验证 Core |
