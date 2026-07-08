# CSQIT v11.2.1 — 宇宙的源代码：从离散信息到宇宙密度的形式化演绎

**Causal Structure Quantum Information Theory**

**版本**: v11.2.1  
**日期**: 2026年7月8日  
**Lean 版本**: v4.29.0-rc6（见 [lean-toolchain](lean-toolchain)）  
**编译状态**: 3267 jobs 全部通过  
**代码规模**: 54 个 Lean 文件，约 26,000 行形式化证明

---

## 项目简介

CSQIT（因果结构量子信息理论）是一个在 **Lean 4** 证明助手中完全形式化的离散因果-信息公理框架。从 10 条关于因果关系、规则复合与量子振幅的公理出发，通过机器可验证的形式化证明，推导出可与观测宇宙学对比的数值结果（零自由参数）。

**核心结果**：在 EffectiveFin7Regularity 条件下，公理体系必然给出特征常数 $\theta = 1/(2+2\cos(2\pi/7)) \approx 0.308$，与 Planck 2018 观测的宇宙总物质密度 $\Omega_m \approx 0.311$ 偏差约 1%。

**理论生长脉络**：从 AxiomA 的自包含性（`input_must_be_empty`）作为种子，经过两面性分叉、代数因果序根系扩展、Fin 7 主干生成、射影紧化枝叶展开，最终抵达观测者的自我认知——每一阶段都是前一阶段逻辑必然性的展开。

**六层唯一性锁定框架**：公理闭合 → 两面性冲突 → 素数筛选 → 规范投影 → 参数锚定 → 自指认知

**四闭合环**：代数（三次方程 $\theta^3 - 6\theta^2 + 5\theta - 1 = 0$）→ 几何（3x3 仿射平面）→ 物理（$\Omega_m$）→ 生物（DNA 碱基）

**三锁统一闭环**（新增）：电磁锁（137+9/250）→ 宇宙锁（420/289）→ 引力锁（编织弹性模量）

**论文**（位于 `papers/` 目录）：
- 英文版（PDF）: [The Source Code of the Universe](papers/CSQIT_SourceCodeOfUniverse_en_v11.2.0.pdf)
- 中文版（PDF）: [宇宙的源代码](papers/CSQIT_宇宙的源代码_zh_v11.2.0.pdf)
- LaTeX源文件（英文）: [CSQIT_SourceCodeOfUniverse_en_v11.2.0.tex](papers/CSQIT_SourceCodeOfUniverse_en_v11.2.0.tex)
- LaTeX源文件（中文）: [CSQIT_宇宙的源代码_zh_v11.2.0.tex](papers/CSQIT_宇宙的源代码_zh_v11.2.0.tex)
- Markdown版（英文）: [CSQIT_SourceCodeOfUniverse_en_v11.2.0.md](papers/CSQIT_SourceCodeOfUniverse_en_v11.2.0.md)
- Markdown版（中文）: [CSQIT_宇宙的源代码_zh_v11.2.0.md](papers/CSQIT_宇宙的源代码_zh_v11.2.0.md)
- 参考文献: [references.bib](papers/references.bib)

---

## 验证状态

### W1 层（形式化数学 — 机器可验证）

| 命题 | 证明状态 | 代码位置 |
|------|---------|---------|
| AxiomA-K 公理体系内部自洽 | 严格证明 | [Core/Consistency.lean](Core/Consistency.lean) |
| Fin 7 非平凡模型满足全部公理 | 严格证明 | [Core/Models/EnhancedModels.lean](Core/Models/EnhancedModels.lean) |
| input_must_be_empty（自包含性定理） | 严格证明 | [Core/CausalWeaving.lean](Core/CausalWeaving.lean) |
| 两面性二一定理（离散互补性） | 严格证明 | [Core/TwoAspectTheorems.lean](Core/TwoAspectTheorems.lean) |
| 代数因果序传递性 | 严格证明 | [Core/AlgebraicCausality.lean](Core/AlgebraicCausality.lean) |
| causal_past_trans（因果过去传递性） | 严格证明 | [Core/FoundationalGrowth.lean](Core/FoundationalGrowth.lean) |
| θ = 1/(2+2cos(2π/7)) 代数推导 | 严格证明 | [Core/B_V_Naturalness.lean](Core/B_V_Naturalness.lean) |
| 总物质 = 可见物质 ∪ 暗物质 | 严格证明 | [Core/DarkUniverse.lean](Core/DarkUniverse.lean) |
| 循环代数稳定子结构 | 严格证明 | [Core/Models/FiniteWeavingExamples.lean](Core/Models/FiniteWeavingExamples.lean) |
| 热力学第二定律（离散版） | 严格证明 | [Core/ThermodynamicArrow.lean](Core/ThermodynamicArrow.lean) |
| 过去假设定理 | 严格证明 | [Core/ThermodynamicArrow.lean](Core/ThermodynamicArrow.lean) |
| 电势差与两面极化等价性 | 严格证明 | [Unified/Models/Electrostatics.lean](Unified/Models/Electrostatics.lean) |
| 磁性与自旋态模型 | 严格证明 | [Unified/Models/Magnetism.lean](Unified/Models/Magnetism.lean) |
| 导电率与元素关系模型 | 严格证明 | [Unified/Models/Conductivity.lean](Unified/Models/Conductivity.lean) |
| 固液气三态模型 | 严格证明 | [Unified/Models/PhaseStates.lean](Unified/Models/PhaseStates.lean) |
| 固体透明原理模型 | 严格证明 | [Unified/Models/Transparency.lean](Unified/Models/Transparency.lean) |

### W2/W3 层（有效理论/物理诠释）

| 命题 | 当前状态 | 层级 | 代码位置 |
|------|---------|------|---------|
| θ ≈ Ω_m（与观测偏差 ~1%） | 经验锚点 | W2/W3 | [Core/B_V_Naturalness.lean](Core/B_V_Naturalness.lean) |
| θ(p) 展开谱严格单调递减 | 数值验证 | W2 | [Core/B_V_Naturalness.lean](Core/B_V_Naturalness.lean) |
| p=7 在结构形成窗口 (0.28, 0.33) 内唯一 | 数值验证 | W2 | [Core/B_V_Naturalness.lean](Core/B_V_Naturalness.lean) |
| Regge → 爱因斯坦-希尔伯特收敛性 | 框架完整，证明待填充 | W2 | [FutureWork/Appendices/AppendixC/Regge.lean](FutureWork/Appendices/AppendixC/Regge.lean) |
| SU(3)×SU(2)×U(1) 完整李代数 | 仅 su(3) Cartan | W2/W3 | [Core/TwoAspectToSU2.lean](Core/TwoAspectToSU2.lean) |
| **精细结构常数精确解 1/α = 137 + 9/250** | 严格证明 | W2/W3 | [Unified/Constants/FineStructure.lean](Unified/Constants/FineStructure.lean) |
| **ΛCDM宇宙组分整数比 20:111:289** | 严格证明 | W2/W3 | [Unified/Constants/LambdaCDM.lean](Unified/Constants/LambdaCDM.lean) |
| **哈勃常数 H₀ ≈ 67.39475 km/s/Mpc** | 严格证明 | W2/W3 | [Unified/Constants/Hubble.lean](Unified/Constants/Hubble.lean) |
| **引力常数作为编织弹性模量** | 严格证明 | W2/W3 | [Unified/Constants/Gravity.lean](Unified/Constants/Gravity.lean) |

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

### 三锁统一闭环（新增）

| 锁 | 数值 | 物理意义 | 代码位置 |
|:---:|:---:|:---:|:---:|
| 第一锁（电磁） | 137 + 9/250 | 精细结构常数倒数 | [Unified/Constants/FineStructure.lean](Unified/Constants/FineStructure.lean) |
| 观测者桥 | 250/9 | 测量代价的对偶 | [Unified/Constants/FineStructure.lean](Unified/Constants/FineStructure.lean) |
| 第二锁（宇宙） | 20:111:289 | 宇宙组分整数比 | [Unified/Constants/LambdaCDM.lean](Unified/Constants/LambdaCDM.lean) |
| 全闭包公分母 | 420 = 2²×3×5×7 | 五大基本常数乘积 | [Unified/Constants/LambdaCDM.lean](Unified/Constants/LambdaCDM.lean) |
| 第三锁（哈勃） | H₀ ≈ 67.39475 | 宇宙膨胀率 | [Unified/Constants/Hubble.lean](Unified/Constants/Hubble.lean) |
| 生长链阻尼 | 61/30 = 2 + 1/30 | 膨胀摩擦因子 | [Unified/Constants/Hubble.lean](Unified/Constants/Hubble.lean) |
| 引力闭包 | G ∝ 1/M_P0² | 编织弹性模量 | [Unified/Constants/Gravity.lean](Unified/Constants/Gravity.lean) |

---

## 项目结构

```
CSQIT/
├── Core/                              # 核心公理层（W1，约38个文件）
│   ├── Axioms.lean                   # 公理体系 A-K 定义
│   ├── Consistency.lean              # 一致性证明
│   ├── FoundationalGrowth.lean       # 基础生长与因果过去
│   ├── CausalWeaving.lean            # 因果编织
│   ├── CausalLattice.lean            # 因果格
│   ├── TwoAspectTheorems.lean        # 两面性二一定理
│   ├── TwoAspectToSU2.lean           # 两面性 → SU(2) 对应
│   ├── AlgebraicCausality.lean       # 代数因果序
│   ├── B_V_Naturalness.lean          # Fin 7 与 θ 推导
│   ├── DarkUniverse.lean             # 暗宇宙分类
│   ├── ScaleDynamics.lean            # 尺度动力学与统一作用量
│   ├── ThermodynamicArrow.lean       # 时间箭头
│   ├── QuantumMeasurement.lean       # 量子测量
│   ├── HierarchicalWeaving.lean      # 层级编织
│   ├── HierarchicalLevels.lean       # 层级结构
│   ├── HDST.lean                     # 高维时空结构
│   ├── ShellCapacityDerivation.lean  # 壳层容量推导
│   ├── Unified.lean                  # 统一框架
│   ├── Theorems.lean                 # 核心定理汇总
│   ├── OpenProblems.lean             # 开放问题
│   ├── Models/                       # 模型目录（7 个文件）
│   │   ├── EnhancedModels.lean       # 增强模型（fin7Model, fin8Model）
│   │   ├── FinModels.lean            # 有限模型
│   │   ├── Fin8Growth.lean           # Fin 8 生长模型
│   │   ├── FiniteWeavingExamples.lean# 层级编织实例
│   │   ├── PeriodicTable.lean        # 周期表对应
│   │   └── TwoAspectBalancedVerification.lean  # 两面性平衡验证
│   └── ...
├── Unified/                           # 统一闭包层（核心成果）
│   ├── Constants/                    # 三锁统一常数（W1完成态，4个文件）
│   │   ├── FineStructure.lean        # 第一锁：精细结构常数 1/α = 137 + 9/250
│   │   ├── LambdaCDM.lean            # 第二锁：ΛCDM组分 20:111:289
│   │   ├── Hubble.lean               # 第三锁：哈勃常数 H₀ ≈ 67.39475
│   │   └── Gravity.lean              # 引力闭包：编织弹性模量 G
│   └── Models/                       # 应用物理模型（W2/W1应用态，5个文件）
│       ├── Electrostatics.lean       # 电势差与两面极化
│       ├── Magnetism.lean            # 磁性与自旋态模型
│       ├── Conductivity.lean         # 导电率与能带结构
│       ├── PhaseStates.lean          # 固液气三态模型
│       └── Transparency.lean         # 固体透明原理
├── Appendices/                       # 基础附录模块（A-E）
│   ├── AppendixA/Uniqueness.lean     # A: 唯一性
│   ├── AppendixB/CausalAndProbability.lean  # B: 因果与概率
│   ├── AppendixC/CausalStructure.lean # C: 因果结构
│   ├── AppendixD/BlackHoleThermo.lean # D: 黑洞热力学
│   └── AppendixE/Mathematics.lean    # E: 数学基础
├── FutureWork/                       # 探索性工作（W2/W3概念态）
│   ├── Appendices/                   # 概念附录（J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z）
│   │   ├── AppendixJ/                # 电势差模型
│   │   ├── AppendixM/                # 磁性模型
│   │   ├── AppendixO/                # 导电率模型
│   │   ├── AppendixP/                # 物态模型
│   │   ├── AppendixR/                # 透明度模型
│   │   ├── AppendixW-Z/              # 三锁统一旧路径（保留供兼容）
│   │   └── ...                       # 其余探索性附录
│   └── README.md                     # FutureWork 说明文档
├── papers/                           # 论文预印本与源文件
│   ├── CSQIT_SourceCodeOfUniverse_en_v11.2.0.pdf  # 英文完整版 PDF
│   ├── CSQIT_宇宙的源代码_zh_v11.2.0.pdf          # 中文完整版 PDF
│   ├── CSQIT_SourceCodeOfUniverse_en_v11.2.0.tex  # 英文 LaTeX 源文件
│   ├── CSQIT_宇宙的源代码_zh_v11.2.0.tex          # 中文 LaTeX 源文件
│   ├── CSQIT_SourceCodeOfUniverse_en_v11.2.0.md   # 英文 Markdown 版
│   ├── CSQIT_宇宙的源代码_zh_v11.2.0.md           # 中文 Markdown 版
│   └── references.bib                              # 参考文献
├── lakefile.lean                     # Lake 项目配置
├── lean-toolchain                    # Lean 版本锁定
├── LICENSE.txt                       # MIT 许可证
├── .gitignore                        # Git 忽略规则
└── README.md                         # 本文件
```

---

## 核心公理体系（A-K）

| 公理 | 描述 | 状态 |
|------|------|------|
| **AxiomA** | 关系元与规则的定义 | W1 完备 |
| **AxiomB** | 因果偏序 | W1 完备 |
| **AxiomC** | 量子振幅（复数幺正表示） | W1 完备 |
| **AxiomD** | 操作编织 | W1 完备（与 AxiomC 有 trade-off） |
| **AxiomE** | 信息容量 | W1 完备 |
| **AxiomF** | 连续极限 | W2 框架定义，实例退化 |
| **AxiomG** | 量子引力耦合 | W2 框架定义，实例退化 |
| **AxiomH** | 规范群嵌入 | W2 框架定义，实例退化 |
| **AxiomI** | 信息因果性 | W1 完备 |
| **AxiomJ** | 动力学演化 | W1 完备 |
| **AxiomK** | 永恒此刻（尺度动力学） | W1 定义，部分推论 |

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
# 预期输出：3267 jobs, 0 errors
```

### 编译三锁统一模块

```bash
# 编译精细结构常数（第一锁）
lake build Unified.Constants.FineStructure

# 编译ΛCDM宇宙组分（第二锁）
lake build Unified.Constants.LambdaCDM

# 编译哈勃常数（第三锁）
lake build Unified.Constants.Hubble

# 编译引力常数（引力闭包）
lake build Unified.Constants.Gravity
```

---

## 经验锚点

在两面性诠释下，从公理体系推导出的特征常数：

$$\theta = \frac{1}{2 + 2\cos(2\pi/7)} \approx 0.308$$

该常数满足三次方程 $\theta^3 - 6\theta^2 + 5\theta - 1 = 0$，与 Planck 2018 观测值 $\Omega_m = 0.311$ 的偏差约 1%。这是从纯公理到可观测数值的完整演绎链（零自由参数），作为经验锚点表明该框架可能与真实物理有关。

**扩展统一身份方程**：$7 \equiv 15 \mod 8 \to \theta = 0.308 \to \Omega_m = 0.311 \to 4\text{ DNA 碱基} \to 8\text{ SU(3) 生成元}$

**三锁统一（新增）**：从基本常数 {2,3,4,5,7} 出发，严格推导出：
- 精细结构常数：$1/\alpha = 137 + 9/250$
- 宇宙组分：$\Omega_b:\Omega_{DM}:\Omega_\Lambda = 20:111:289$（公分母 420）
- 哈勃常数：$H_0 \approx 67.39475$ km/s/Mpc
- 引力常数：$G \propto 1/M_{P0}^2$，完成"量子-宇宙-引力"三位一体

---

## 诚实边界声明

1. **所有定理均证明于有限类型**（Fin n, Unit, Bool）
2. **"θ = Ω_m" 是物理解释**（W2/W3），而非数学定理（W1）
3. **连续极限收敛性是开放问题**
4. **不声称已统一量子力学和广义相对论**
5. **代码中保留 4 个 sorry 作为数学不可能性的反例标记**
6. **三锁统一中的单位编织量子 G_unit 尚未从公理导出**（留作未来工作）

---

## 版本演进

| 日期 | 版本 | 主要改进 |
|:---|:---|:---|
| 2026-06-19 | 10.4.5 | 初始版本 |
| 2026-06-22 | 10.5 | W1/W2/W3 分层 |
| 2026-06-28 | 11.0.0 | 因果格、量子测量、时间箭头 |
| 2026-07-01 | 11.1.0 | Fin 7 θ 推导 |
| 2026-07-04 | 11.2.0 | 生长叙事、代数因果序、射影紧化、2196 jobs 通过 |
| 2026-07-08 | 11.2.1 | **三锁统一闭环**：精细结构常数、ΛCDM组分、哈勃常数、引力常数形式化证明；架构重构为Core/Unified/FutureWork三层 |

---

## 许可证

MIT License

---

*CSQIT v11.2.1 — 宇宙的源代码：从离散信息到宇宙密度的形式化演绎*  
*Lean 4 v4.29.0-rc6 — 3267 编译任务，0 错误*  
*三锁统一闭环 — 量子·宇宙·引力三位一体*
