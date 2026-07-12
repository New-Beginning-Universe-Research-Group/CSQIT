# 目录结构、命名规范与命名空间统一

> 更新时间：2026-07-12 | 版本：v11.6.0

---

## 一、目录结构规范

### 1. 核心目录结构

```
CSQIT/
├── Core/                          # 核心公理体系
│   ├── W1/                        # W1 形式化数学核心（25 文件）
│   │   ├── Models/                # 有限模型（1 文件）
│   │   ├── Axioms.lean            # 公理体系 A-K 定义
│   │   ├── WeavingStructure.lean  # 编织结构（seq + par + interchange）
│   │   ├── ThreeGroupHierarchy.lean # 三群谱系统一定义
│   │   ├── Consistency.lean       # 一致性证明
│   │   └── ...
│   ├── W2/                        # W2 有效理论（19 文件）
│   │   ├── Models/                # 增强模型（3 文件）
│   │   ├── Integration.lean       # v11/v12 整合（seq/par 带类型）
│   │   ├── ContinuumLimit.lean    # 连续极限
│   │   ├── PhysicalConstants.lean # 物理常数
│   │   └── ...
│   └── W3/                        # W3 探索性框架（6 文件）
│       ├── Core.lean              # 操作本体论核心
│       ├── Models.lean            # 操作模型
│       ├── AtomicOperations.lean  # 原子操作
│       ├── UnifiedPicture.lean    # 统一图景
│       ├── CyclicUniverse.lean    # 循环宇宙
│       └── Summary.lean           # 总结
├── Unified/                       # 统一闭包层（待整理）
│   ├── Constants/                 # 三锁统一常数
│   └── Models/                    # 应用物理模型
├── Appendices/                    # 附录（待整理）
│   ├── AppendixA/
│   ├── AppendixB/
│   └── ...
├── papers/                        # 论文预印本
├── docs/                          # 项目文档
│   ├── THEORY_AND_CODE_OPTIMIZATION.md
│   └── PROJECT_STRUCTURE.md       # （本文件）
├── PROJECT_STATUS.md              # 项目状态清单（实时更新）
├── lakefile.lean                  # Lake 项目配置
├── lean-toolchain                 # Lean 版本锁定
└── README.md                      # 项目介绍
```

### 2. W1/W2/W3 分层原则

| 层级 | 名称 | 标准 | 验证要求 |
|------|------|------|----------|
| **W1** | 形式化数学核心 | 从公理出发的严格证明 | 100% Lean 机器验证，无 sorry |
| **W2** | 有效理论 | 有定义、有框架、有部分证明 | 核心结构编译通过，允许少量 sorry 标记缺口 |
| **W3** | 探索性框架 | 概念定义、猜想、非形式化论证 | 编译通过即可，证明可以是框架性的 |

### 3. 子目录约定

- `Models/`：具体模型构造（Fin n 等），用于验证和举例
- `Constants/`：物理常数相关的推导
- 同一层级下的文件应尽量扁平，避免过深嵌套

---

## 二、文件命名规范

### 1. 命名原则

- **描述性命名**：文件名描述内容，不含版本号
- **大驼峰**：Lean 文件名使用 PascalCase（与模块名一致）
- **不加版本前缀**：v12Core → Core，v115CyclicUniverse → CyclicUniverse
- **版本号只在文件头部元数据中体现**

### 2. 命名空间与文件名对应

```
Core/W1/WeavingStructure.lean  →  CSQIT.W1.WeavingStructure
Core/W2/Integration.lean       →  CSQIT.W2.Integration
Core/W3/Core.lean              →  CSQIT.W3.Core
```

- 目录路径 `.` 分隔后就是命名空间
- `Core` 目录对应 `CSQIT` 顶层命名空间
- 每个 `.lean` 文件对应一个模块

### 3. 命名空间统一规则

**旧命名空间 → 新命名空间映射**：

| 旧命名空间 | 新命名空间 | 说明 |
|-----------|-----------|------|
| `Core.xxx` | `CSQIT.W1.xxx` 或 `CSQIT.W2.xxx` | 按层级归属 |
| `Core.v115.xxx` | `CSQIT.W2.xxx` | v115 内容大多归 W2 |
| `Core.v12.xxx` | `CSQIT.W3.xxx` | v12 探索框架归 W3 |
| `Unified.xxx` | `CSQIT.Wx.xxx` | 待整理后确定 |

### 4. import 路径规范

- 永远使用完整命名空间引用：`import CSQIT.W1.ThreeGroupHierarchy`
- 不要使用相对路径导入
- 跨层级导入需明确层级：W2 可以 import W1，W3 可以 import W1/W2

---

## 三、文件头部元数据规范

### 1. 标准格式

每个 `.lean` 文件头部必须包含以下格式的元数据注释：

```lean
/-
================================================================================
CSQIT — 核心公理体系（操作本体论）
文件: Core/W1/WeavingStructure.lean
版本: v11.6.0
层级: W1 — 形式化数学核心
行数: 515
编译: ✅ 编译通过 (3331 jobs)
日期: 2026-07-12
================================================================================
[简要描述文件内容和地位]
================================================================================
-/
```

### 2. 字段说明

| 字段 | 必填 | 说明 |
|------|------|------|
| 文件 | ✅ | 从项目根目录开始的相对路径，用 `/` 分隔 |
| 版本 | ✅ | 项目整体版本号，如 `v11.6.0` |
| 层级 | ✅ | `W1 — 形式化数学核心` / `W2 — 有效理论` / `W3 — 探索性框架` |
| 行数 | ✅ | 文件总行数（包括注释和空行） |
| 编译 | ✅ | `✅ 编译通过 (N jobs)` 或 `❌ 编译失败` |
| 日期 | ✅ | 最后修改日期，格式 `YYYY-MM-DD` |

### 3. 版本号规则

- 项目统一版本号，单个文件不单独版本
- 版本号格式：`v主版本.次版本.修订号`
  - 主版本：理论框架重大变更（如 v11 → v12 是操作本体论转换）
  - 次版本：新模块/新定理加入
  - 修订号：bug修复、优化、文档更新

### 4. 层级标签速查

| 标签 | 含义 | 标准 |
|------|------|------|
| W1 | 形式化数学核心 | 100% 机器证明，无 sorry |
| W2 | 有效理论 | 核心定义+部分证明，允许少量 sorry |
| W3 | 探索性框架 | 概念和框架，编译通过即可 |

---

## 四、注释规范

### 1. 注释类型

| 类型 | 语法 | 用途 |
|------|------|------|
| 模块注释 | `/- ... -/` | 文件头部元数据和整体说明 |
| 文档字符串 | `/-! ... -/` | 定理/定义的正式文档（用于生成文档） |
| 普通注释 | `-- ...` | 行内说明 |
| 区块注释 | `/- ... -/` | 多行说明 |

### 2. 注释语言

- 注释使用中文（与项目文档语言一致）
- 代码标识符使用英文
- 数学符号使用 LaTeX 或 Unicode 数学符号

### 3. 路径引用规范

- 在注释中引用其他文件时，使用相对路径
- 格式：`Core/W1/ThreeGroupHierarchy.lean`
- 不使用旧版本路径（如 `Core/v115/xxx.lean`、`Core/v12/xxx.lean`）

---

## 五、代码组织约定

### 1. 文件内结构顺序

```
1. 头部元数据注释
2. import 语句（按字母顺序）
3. 命名空间声明（`namespace CSQIT.W1.xxx`）
4. 类型定义
5. 核心定义
6. 定理/引理
7. 示例/模型
8. 命名空间关闭（`end CSQIT.W1.xxx`）
```

### 2. 定义集中化原则

- **核心数学定义单点定义**：如三群阶、totalClosure 等，在一个文件中定义，其他文件 import 使用
- **避免重复定义**：同一概念在多个文件中定义会导致漂移和不一致
- **定义的权威来源**：
  - 三群谱系：`Core/W1/ThreeGroupHierarchy.lean`
  - 编织结构：`Core/W1/WeavingStructure.lean`
  - 公理体系：`Core/W1/Axioms.lean`

### 3. 死代码处理

- 不再维护的代码移动到 `_archive/` 目录（或删除）
- lakefile.lean 中移除对应 root
- 在 PROJECT_STATUS.md 中记录归档情况

---

## 六、PROJECT_STATUS.md 维护规范

### 1. 更新时机

每次 `lake build` 成功后更新。

### 2. 必须更新的内容

- 编译状态和 jobs 数
- Sorry 语句统计（如有变化）
- 文件列表和行数（如有增减）
- 版本号和日期

### 3. 表格维护

- W1/W2/W3 各层级文件列表
- 每个文件的：行数、层级、编译状态、完成度、待办
- Sorry 清单（文件、位置、数量、类型、描述）
- 待办事项（按优先级）
- 编译统计（耗时、总jobs、成功、失败）

---

## 七、lakefile.lean 配置规范

### 1. roots 组织方式

roots 按 W1 → W2 → W3 顺序排列，每个层级内用注释分隔：

```lean
roots := #[
  -- ===== W1：形式化数学核心 =====
  `CSQIT.W1.Axioms,
  `CSQIT.W1.BasicModels,
  ...
  -- ===== W2：有效理论 =====
  `CSQIT.W2.ScaleDynamics,
  ...
  -- ===== W3：探索性框架 =====
  `CSQIT.W3.Core,
  ...
]
```

### 2. 命名约定

- 包名：`CSQIT`
- 模块前缀：`CSQIT.W1.`、`CSQIT.W2.`、`CSQIT.W3.`
- 版本号：与项目版本一致

---

## 八、历史变更记录

### v11.6.0（2026-07-12）

- 目录按 W1/W2/W3 重新组织，移除 v115/v12 版本文件夹
- W3 文件名去版本前缀（v12Core → Core 等）
- 命名空间统一为 CSQIT.W1 / CSQIT.W2 / CSQIT.W3
- 版本号统一为 v11.6.0
- 文件头部元数据标准化
- 新增 PROJECT_STATUS.md 项目状态清单
- 群阶和 totalClosure 统一定义到 ThreeGroupHierarchy.lean
- 新增 docs/ 目录存放项目文档

### v11.5.0 及以前

- 版本号体现在目录结构（v115/、v12/）
- 命名空间不统一（Core.xxx、Core.v115.xxx、Core.v12.xxx）
- 群阶定义分散在多个文件
- 无统一的头部元数据格式
