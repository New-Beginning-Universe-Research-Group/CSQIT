# CSQIT v11.6.0 工作流（第二版）

**版本**: v2.0  
**日期**: 2026-07-15  
**工作目录**: `D:\CSQIT-workspace\CSQIT_v11.2.6_final\`  
**WSL 项目路径**: `~/CSQIT_Refactor/`  
**WSL 发行版**: `Ubuntu_24.04.1_LTS`  

---

## 一、目录约定

| 目录 | 用途 | 操作权限 |
|------|------|---------|
| `D:\CSQIT-workspace\CSQIT_v11.2.6_final\` | **唯一工作目录** | 可读可写 |
| `D:\CSQIT-workspace-refactor\` | 备份目录（WSL 同步源） | 仅读，不修改 |
| `D:\CSQIT-workspace\` (根目录) | 备份/临时文件 | 仅存放临时脚本 |
| `~/CSQIT_Refactor/` (WSL) | 编译环境 | 编译验证用 |

**原则**：所有代码修改在工作目录完成，然后同步到 WSL 编译验证。

---

## 二、标准工作流

### 2.1 修改-编译-验证循环

```
┌─────────────────────────────────────────────────────────┐
│  1. 在工作目录 (Windows) 修改 .lean 文件                 │
│     路径: D:\CSQIT-workspace\CSQIT_v11.2.6_final\       │
└────────────────────────┬────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────┐
│  2. 同步到 WSL                                          │
│     命令: wsl_sync.ps1 或 rsync                         │
└────────────────────────┬────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────┐
│  3. WSL 编译验证                                        │
│     lake build <ModuleName>                             │
│     成功 → 继续 / 失败 → 回到步骤1修复                  │
└────────────────────────┬────────────────────────────────┘
                         │
                         ▼
┌─────────────────────────────────────────────────────────┐
│  4. 提交 Git (WSL 中)                                    │
│     git add / git commit / git push                     │
└─────────────────────────────────────────────────────────┘
```

### 2.2 同步命令（Windows → WSL）

在 PowerShell 中执行：

```powershell
# 同步工作目录到 WSL
& 'C:\Windows\System32\wsl.exe' -d Ubuntu_24.04.1_LTS -- bash -c @"
rsync -av --no-perms --no-owner --no-group \
  --exclude='.git' --exclude='.lake' \
  /mnt/d/CSQIT-workspace/CSQIT_v11.2.6_final/ \
  ~/CSQIT_Refactor/
"@
```

**关键参数说明**：
- `--no-perms --no-owner --no-group`: 避免 DrvFS 权限问题
- `--exclude='.lake'`: 排除编译缓存
- `-a`: 归档模式（递归 + 保留时间戳）

### 2.3 编译验证命令

```bash
# 编译单个模块
lake build Core.W1.Independence

# 编译多个模块
lake build Core.W1.Axioms Core.W1.WeavingStructure

# 编译整个项目
lake build

# 快速检查（仅检查错误，不生成缓存）
lake build --no-build
```

---

## 三、项目分层与编译标准

### 3.1 W1 层（形式化数学核心）

**标准**：零 `sorry`、零 `admit`、所有证明可机器检查

**模块清单**（25 个）：
- 核心公理：`Axioms.lean`, `BasicModels.lean`
- 因果结构：`CausalLattice.lean`, `CausalWeaving.lean`, `WeavingStructure.lean`
- 代数结构：`AlgebraicCausality.lean`, `TwoAspectToSU2.lean`, `TwoAspectTheorems.lean`
- 振幅理论：`AmplitudeTheorems.lean`
- 层级结构：`HierarchicalLevels.lean`, `HierarchicalWeaving.lean`, `Hierarchy.lean`
- 生长理论：`FoundationalGrowth.lean`, `GrowthToAxioms.lean`
- 一致性：`Consistency.lean`
- 独立性：`AxiomC_Independence.lean`, `AxiomD_Independence.lean`, `Independence.lean`
- 其他：`BasicProperties.lean`, `ThreeGroupHierarchy.lean`, `ShellCapacityDerivation.lean`
- 模型：`Models/FinModels.lean`
- 桥梁：`CausalLatticeToAxiomA.lean`, `CausalSetCorrespondence.lean`
- 统一：`Unified.lean`

### 3.2 W2 层（有效理论）

**标准**：核心定理零 `sorry`，探索性内容可用 `def : Prop :=` 标注

**模块清单**（16 个）：
- 尺度动力学：`ScaleDynamics.lean`, `B_V_Naturalness.lean`
- 时空结构：`HDST.lean`, `ContinuumLimit.lean`
- 整合：`Integration.lean`, `Summary.lean`
- 生长模型：`GrowthModel.lean`, `GrowthAndSymmetry.lean`
- 物理常数：`PhysicalConstants.lean`, `ThreeLocksDerivation.lean`
- 严格推导：`StrictDerivation.lean`, `GravityDerivation.lean`
- 群表示：`GroupRepresentationData.lean`
- 模型：`Models/EnhancedModels.lean`, `Models/PeriodicTable.lean`, `Models/FiniteWeavingExamples.lean`

### 3.3 W3 层（探索性框架）

**标准**：允许 `sorry` 和概念性内容，明确标注探索性质

**模块清单**（6 个）：
- `Core.lean`, `Models.lean`, `AtomicOperations.lean`
- `UnifiedPicture.lean`, `CyclicUniverse.lean`, `Summary.lean`

---

## 四、任务优先级

### P0（最高优先级，必须完成）

| 任务 | 说明 | 涉及文件 |
|------|------|---------|
| 修复 Independence.lean 编译 | 取消 lakefile 注释，修复编译错误 | `Core/W1/Independence.lean` |
| 修复 CausalLatticeToAxiomA.lean 编译 | 取消注释，修复编译错误 | `Core/W1/CausalLatticeToAxiomA.lean` |
| 修复 CausalSetCorrespondence.lean 编译 | 取消注释，修复编译错误 | `Core/W1/CausalSetCorrespondence.lean` |
| 建立 Unified/Models 与 W1 的连接 | 将 Electrostatics 等与 W1 公理体系连接 | `Unified/Models/*.lean` (4个) |

### P1（高优先级）

| 任务 | 说明 | 涉及文件 |
|------|------|---------|
| CausalLattice.lean 的 exact? 手写化 | 5 处 exact? 改为手写证明 | `Core/W1/CausalLattice.lean` |
| ContinuumLimit 3D 曲率上界证明非平凡化 | 从平凡上界改为实质性几何证明 | `Core/W2/ContinuumLimit.lean` |
| W3 层独立编译目标设置 | lakefile 中为 W3 设置独立 target | `lakefile.lean` |

### P2（中优先级）

| 任务 | 说明 | 涉及文件 |
|------|------|---------|
| Unified/Models 数值定理升级为 W1 推导 | 从数值定义升级为公理推导 | `Unified/Models/*.lean` |
| 三群推导从数值验证升级为群论推导 | 严格群论证明 | `Core/W2/StrictDerivation.lean` 等 |

---

## 五、调试技巧

### 5.1 常用 Lean 诊断命令

```bash
# 检查某个文件的语法错误（最快）
lake env lean --stdin < Core/W1/Example.lean

# 仅检查依赖，不编译目标
lake build --dep Core.W1.Axioms

# 查看模块依赖图
lake build --graph
```

### 5.2 常见错误速查

| 错误模式 | 可能原因 | 解决方法 |
|---------|---------|---------|
| `motive is not type correct` | `rw` 在依赖类型索引上 | 用 `simp`、`Eq.ndrec` 或 `subst` |
| `omega could not prove` | 缺少边界条件假设 | 添加 `have h_len : ...` 假设 |
| `type mismatch` | 函数签名不匹配 | 检查类型类实例和参数顺序 |
| `tactic 'apply' failed` | 结论形式不匹配 | 先用 `have` 构造中间结论 |

### 5.3 降维打击方法论

当遇到复杂证明时，优先考虑：
1. **定义展开**：直接用定义重写，而非寻找高级定理
2. **代数化简**：`ring_nf`、`simp`、`omega` 先把目标化简
3. **分情况**：`if` 或 `by_cases` 把复杂目标拆成简单子目标
4. **反方向**：从结论倒推需要什么前提
5. **已证定理复用**：搜索同文件中类似的证明模式

---

## 六、版本与提交规范

### 6.1 版本号

使用语义化版本：`v11.6.x`
- 主版本 `11`：CSQIT 大版本
- 次版本 `6`：架构重构版本（W1/W2/W3 分层）
- 补丁号 `x`：bug 修复和增量改进

### 6.2 Git 提交信息

```
<type>(<scope>): <subject>

type:
  feat:     新功能/新定理
  fix:      修复编译错误或证明漏洞
  refactor: 代码重构，不改变语义
  docs:     文档更新
  chore:    构建配置、工具链更新

scope:
  W1: 核心公理层
  W2: 有效理论层
  W3: 探索框架层
  unified: Unified 目录
  build: 构建系统

例子:
  fix(W1): eliminate sorry in WeavingStructure.comp
  feat(W2): prove scalarCurvature3D upper bound
  refactor(build): reorganize lakefile roots by layer
```

---

## 七、项目完成标准

### 7.1 核心完成标志

- [ ] W1 层全部 25 个模块编译通过，零 `sorry`
- [ ] W2 层核心定理编译通过，非平凡证明
- [ ] `Unified/Models/` 与 W1 公理体系建立显式连接
- [ ] `lake build` 全项目编译通过

### 7.2 质量标准

- W1 层：100% 证明覆盖率，零 `sorry`，零 `exact?`（可选）
- W2 层：核心定理有完整证明，探索内容明确标注
- W3 层：概念清晰，与 W1/W2 的边界明确

---

*本工作流文档为活文档，随项目进展持续更新。*
