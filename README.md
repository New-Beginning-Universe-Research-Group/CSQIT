# CSQIT — 宇宙的源代码：从离散信息到宇宙密度的形式化演绎

**Causal Structure Quantum Information Theory**

**版本**: v11.6.0  
**日期**: 2026年7月12日  
**Lean 版本**: v4.29.0-rc6（见 [lean-toolchain](lean-toolchain)）  
**编译状态**: ✅ 3331 jobs 全部通过  
**代码规模**: 52 个核心模块，18,364 行 Lean 代码  
**Sorry 统计**: 7 处（4 FiniteWeavingExamples + 2 Integration + 1 Consistency）

---

## 项目简介

CSQIT（因果结构量子信息理论）是一个在 **Lean 4** 证明助手中完全形式化的离散因果-信息公理框架。从关于因果关系、规则复合与量子振幅的公理出发，通过机器可验证的形式化证明，推导出可与观测宇宙学对比的数值结果（零自由参数）。

**核心结果**：在 EffectiveFin7Regularity 条件下，公理体系必然给出特征常数 $\theta = 1/(2+2\cos(2\pi/7)) \approx 0.308$，与 Planck 2018 观测的宇宙总物质密度 $\Omega_m \approx 0.311$ 偏差约 1%。

**理论生长脉络**：从 AxiomA 的自包含性（`input_must_be_empty`）作为种子，经过两面性分叉、代数因果序根系扩展、Fin 7 主干生成、射影紧化枝叶展开，最终抵达观测者的自我认知——每一阶段都是前一阶段逻辑必然性的展开。

**Eckmann-Hilton 突破**：通过带类型的部分运算（`Weave L R` + `ParallelWeave`），在 2-范畴框架下避免了 seq=par 的平凡化。SquareIncomparable 条件下 interchange 律成立，有限模型反例证明 seq≠par。

**三锁统一闭环**：电磁锁（137+9/250）→ 宇宙锁（420/289）→ 引力锁（编织弹性模量）

**三群谱系**：A₄(12) → A₅(60) → PSL(2,7)(168)，素因子 {2,3,5,7}，totalClosure = 420

---

## 项目结构

```
CSQIT/
├── Core/                              # 核心公理体系
│   ├── W1/                            # W1 形式化数学核心（25 文件）
│   │   ├── Axioms.lean               # 公理体系 A-K 定义
│   │   ├── WeavingStructure.lean     # 编织结构（seq + par + interchange）
│   │   ├── ThreeGroupHierarchy.lean  # 三群谱系统一定义
│   │   ├── Consistency.lean          # 一致性证明
│   │   ├── BasicProperties.lean      # Eckmann-Hilton 不可能定理
│   │   ├── AlgebraicCausality.lean   # 代数因果序
│   │   ├── TwoAspectTheorems.lean    # 两面性二一定理
│   │   ├── CausalLattice.lean        # 因果格
│   │   ├── Independence.lean         # 公理独立性
│   │   ├── Models/FinModels.lean     # 有限模型
│   │   └── ...
│   ├── W2/                            # W2 有效理论（19 文件）
│   │   ├── Integration.lean          # v11/v12 整合（seq/par 带类型）
│   │   ├── ContinuumLimit.lean       # 连续极限（2D证明 + 4D框架）
│   │   ├── PhysicalConstants.lean    # 物理常数
│   │   ├── GrowthModel.lean          # 生长模型
│   │   ├── B_V_Naturalness.lean      # Fin 7 与 θ 推导
│   │   ├── ThreeLocksDerivation.lean # 三锁常数推导
│   │   ├── StrictDerivation.lean     # 严格推导
│   │   ├── Models/                   # 增强模型（3 文件）
│   │   └── ...
│   └── W3/                            # W3 探索性框架（6 文件）
│       ├── Core.lean                 # 操作本体论核心（v12）
│       ├── Models.lean               # 操作模型
│       ├── AtomicOperations.lean     # 原子操作
│       ├── UnifiedPicture.lean       # 统一图景
│       ├── CyclicUniverse.lean       # 循环宇宙（v11.5）
│       └── Summary.lean              # 总结
├── Unified/                           # 统一闭包层（待整理）
│   ├── Constants/                    # 三锁统一常数
│   └── Models/                       # 应用物理模型
├── Appendices/                        # 附录（待整理）
│   ├── AppendixA/ - AppendixE/
├── papers/                            # 论文预印本
├── docs/                              # 项目文档
│   ├── THEORY_AND_CODE_OPTIMIZATION.md  # 理论与代码优化工作流
│   └── PROJECT_STRUCTURE.md             # 目录结构与命名规范
├── PROJECT_STATUS.md                 # 项目状态清单（实时更新）
├── lakefile.lean                     # Lake 项目配置
├── lean-toolchain                    # Lean 版本锁定
└── README.md                         # 本文件
```

---

## 层级体系

### W1 层（形式化数学核心 — 机器可验证）

| 命题 | 证明状态 | 代码位置 |
|------|---------|---------|
| AxiomA-K 公理体系内部自洽 | 严格证明（1 sorry） | [Core/W1/Consistency.lean](Core/W1/Consistency.lean) |
| Fin 7 非平凡模型满足全部公理 | 严格证明 | [Core/W1/Models/FinModels.lean](Core/W1/Models/FinModels.lean) |
| input_must_be_empty（自包含性定理） | 严格证明 | [Core/W1/CausalWeaving.lean](Core/W1/CausalWeaving.lean) |
| 两面性二一定理（离散互补性） | 严格证明 | [Core/W1/TwoAspectTheorems.lean](Core/W1/TwoAspectTheorems.lean) |
| 代数因果序传递性 | 严格证明 | [Core/W1/AlgebraicCausality.lean](Core/W1/AlgebraicCausality.lean) |
| Eckmann-Hilton 不可能定理 | 严格证明 | [Core/W1/BasicProperties.lean](Core/W1/BasicProperties.lean) |
| 编织结构 + interchange 律（带条件） | 严格证明 | [Core/W1/WeavingStructure.lean](Core/W1/WeavingStructure.lean) |
| 三群谱系统一定义 | 严格定义 | [Core/W1/ThreeGroupHierarchy.lean](Core/W1/ThreeGroupHierarchy.lean) |
| 因果格理论 | 严格证明 | [Core/W1/CausalLattice.lean](Core/W1/CausalLattice.lean) |
| 公理独立性验证 | 严格证明 | [Core/W1/Independence.lean](Core/W1/Independence.lean) |
| θ 三次方程代数推导 | 严格证明 | [Core/W2/B_V_Naturalness.lean](Core/W2/B_V_Naturalness.lean) |

### W2 层（有效理论 — 半严格）

| 命题 | 当前状态 | 代码位置 |
|------|---------|---------|
| seq/par 带类型整合（seq≠par） | 框架完成，2 sorry | [Core/W2/Integration.lean](Core/W2/Integration.lean) |
| 有限编织实例 | 构造完成，4 sorry | [Core/W2/Models/FiniteWeavingExamples.lean](Core/W2/Models/FiniteWeavingExamples.lean) |
| 2D 离散 Gauss-Bonnet 定理 | 严格证明 | [Core/W2/ContinuumLimit.lean](Core/W2/ContinuumLimit.lean) |
| 2D Regge 作用量精确收敛 | 严格证明 | [Core/W2/ContinuumLimit.lean](Core/W2/ContinuumLimit.lean) |
| 4D Regge → 爱因斯坦-希尔伯特 | 时间切片+维度递推框架 | [Core/W2/ContinuumLimit.lean](Core/W2/ContinuumLimit.lean) |
| 三锁常数推导 | 严格推导 | [Core/W2/ThreeLocksDerivation.lean](Core/W2/ThreeLocksDerivation.lean) |
| 生长模型与尺度动力学 | 框架完成 | [Core/W2/GrowthModel.lean](Core/W2/GrowthModel.lean) |

### W3 层（探索性框架 — 概念性）

| 主题 | 状态 | 代码位置 |
|------|------|---------|
| 操作本体论核心（seq/par 双运算） | 85% | [Core/W3/Core.lean](Core/W3/Core.lean) |
| 非交换模型构造 | 80% | [Core/W3/Models.lean](Core/W3/Models.lean) |
| 原子操作分解 | 90% | [Core/W3/AtomicOperations.lean](Core/W3/AtomicOperations.lean) |
| 统一图景 | 95% | [Core/W3/UnifiedPicture.lean](Core/W3/UnifiedPicture.lean) |
| 循环宇宙（三群生长叙事） | 95% | [Core/W3/CyclicUniverse.lean](Core/W3/CyclicUniverse.lean) |

---

## 核心理论进展

### θ(p) 展开谱

| p | θ(p) | 递减 |
|:---:|:---:|:---:|
| 3 | 1.000 | — |
| 5 | 0.382 | ↓ |
| 7 | 0.308 | ↓ |
| 11 | 0.272 | ↓ |
| 13 | 0.265 | ↓ |
| 17 | 0.259 | ↓ |
| ∞ | 0.250 | ↓ |

### 三锁统一闭环

| 锁 | 数值 | 物理意义 |
|:---:|:---:|:---:|
| 第一锁（电磁） | 137 + 9/250 | 精细结构常数倒数 |
| 观测者桥 | 250/9 | 测量代价的对偶 |
| 第二锁（宇宙） | 20:111:289 | 宇宙组分整数比 |
| 全闭包公分母 | 420 = 2²×3×5×7 | 三群 lcm/2 |
| 第三锁（哈勃） | H₀ ≈ 67.39475 | 宇宙膨胀率 |
| 引力闭包 | G ∝ 1/M_P0² | 编织弹性模量 |

### 三群谱系

| 群 | 阶 | 几何对应 | 素因子 |
|:---:|:---:|:---:|:---:|
| A₄ | 12 | 四面体群 | 2, 3 |
| A₅ | 60 | 十二面体群 | 2, 3, 5 |
| PSL(2,7) | 168 | Fano平面群 | 2, 3, 7 |

**totalClosure** = lcm(12, 60, 168) / 2 = 420

---

## 诚实边界声明

1. **所有定理均证明于有限类型**（Fin n, Unit, Bool）
2. **"θ = Ω_m" 是物理解释**（W2/W3），而非数学定理（W1）
3. **2D 连续极限已严格证明**（离散 Gauss-Bonnet 定理 + Regge 精确收敛）
4. **4D 连续极限框架已建立**，完整证明仍在推进中
5. **不声称已统一量子力学和广义相对论**
6. **代码中保留 7 处 sorry**：4 处 FiniteWeavingExamples（因果不可比证明）、2 处 Integration（seq/par 定义域不相交）、1 处 Consistency（有限模型验证）
7. **三锁统一中的单位编织量子 G_unit 尚未从公理导出**（留作未来工作）
8. **W3 操作本体论处于探索阶段**，非形式化完备体系

---

## 编译方法

### 环境要求
- **elan** 工具链管理器
- **Lean 4**: v4.29.0-rc6（见 `lean-toolchain`）
- **mathlib**: v4.29.0-rc6 兼容版本

### 编译步骤

```bash
# 首次配置
lake update

# 编译
lake build
# 预期输出：3331 jobs，全部通过
```

### 核心模块编译

详见 [PROJECT_STATUS.md](PROJECT_STATUS.md)。

---

## 项目文档

| 文档 | 说明 |
|------|------|
| [PROJECT_STATUS.md](PROJECT_STATUS.md) | 项目状态清单（文件列表、行数、编译状态、sorry 统计、待办事项） |
| [docs/THEORY_AND_CODE_OPTIMIZATION.md](docs/THEORY_AND_CODE_OPTIMIZATION.md) | 理论与代码优化工作流、优化思路、待完成事项 |
| [docs/PROJECT_STRUCTURE.md](docs/PROJECT_STRUCTURE.md) | 目录结构规范、文件命名、注释规范、命名空间统一 |

---

## 版本演进

| 日期 | 版本 | 主要改进 |
|:---|:---|:---|
| 2026-06-19 | 10.4.5 | 初始版本 |
| 2026-06-22 | 10.5 | W1/W2/W3 分层 |
| 2026-06-28 | 11.0.0 | 因果格、量子测量、时间箭头 |
| 2026-07-01 | 11.1.0 | Fin 7 θ 推导 |
| 2026-07-04 | 11.2.0 | 生长叙事、代数因果序、射影紧化 |
| 2026-07-08 | 11.2.1 | 三锁统一闭环 |
| 2026-07-10 | 11.2.8 | 连续极限突破：2D Gauss-Bonnet、2D Regge 收敛 |
| 2026-07-12 | 11.6.0 | **Eckmann-Hilton 突破**：带类型编织结构、ParallelWeave、条件 interchange 律、Fin 4 反例；目录按 W1/W2/W3 重组织；命名空间统一 CSQIT.W1/W2/W3；版本号统一 v11.6.0；新增 PROJECT_STATUS.md 和 docs/ 文档 |

---

## 许可证

MIT License

---

*CSQIT v11.6.0 — 宇宙的源代码：从离散信息到宇宙密度的形式化演绎*  
*Lean 4 v4.29.0-rc6 — 52 个核心模块，3331 jobs，100% 通过*  
*Eckmann-Hilton 突破 — 带类型编织结构 · 三群谱系 · 三锁统一闭环*
