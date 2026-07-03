# CSQIT v11.2.0 - Causal Structure Quantum Information Theory

**版本**: v11.2.0
**日期**: 2026年7月3日
**Lean 版本**: v4.29.0-rc6（见 [lean-toolchain](lean-toolchain)）
**编译状态**: ✅ 2069 jobs 全部通过

---

## 🌌 项目简介

CSQIT（因果结构量子信息理论）是一个在 **Lean 4** 证明助手中完全形式化的离散因果-信息公理框架。它从一组关于因果关系、规则复合与量子振幅的公理出发，通过机器可验证的形式化证明，推导出可与观测宇宙学对比的数值结果。

**核心方法论**：从少数信息论公理出发，经过机器可验证的形式化证明，推导出与观测可比的数值（零自由参数）。

**论文**：[English](CSQIT_Paper_English_v11.2.0.md) | [中文版](CSQIT_顶刊论文_中文版_v3_最终版.md) | [投稿信](Cover_Letter.md)

---

## 🔍 验证状态

### W1 层（形式化数学 - 机器可验证）

| 命题 | 证明状态 | 代码位置 |
|------|---------|---------|
| AxiomA–J 公理体系内部自洽 | ✅ 严格证明 | [Core/Consistency.lean](Core/Consistency.lean) |
| Fin 7 非平凡模型满足全部公理 | ✅ 严格证明 | [Core/Models/EnhancedModels.lean](Core/Models/EnhancedModels.lean) |
| θ = 1/(2+2cos(2π/7)) 代数推导 | ✅ 严格证明 | [Core/B_V_Naturalness.lean](Core/B_V_Naturalness.lean) |
| 总物质 = 可见物质 ∪ 暗物质 | ✅ 严格证明 | [Core/DarkUniverse.lean](Core/DarkUniverse.lean) |
| 两面性二一定理（离散互补性） | ✅ 严格证明 | [Core/TwoAspectTheorems.lean](Core/TwoAspectTheorems.lean) |
| 代数因果序传递性 | ✅ 严格证明 | [Core/AlgebraicCausality.lean](Core/AlgebraicCausality.lean) |
| 循环代数稳定子结构 | ✅ 严格证明 | [Core/Models/FiniteWeavingExamples.lean](Core/Models/FiniteWeavingExamples.lean) |
| 热力学第二定律（离散版） | ✅ 严格证明 | [Core/ThermodynamicArrow.lean](Core/ThermodynamicArrow.lean) |
| 过去假设定理 | ✅ 严格证明 | [Core/ThermodynamicArrow.lean](Core/ThermodynamicArrow.lean) |

### W2/W3 层（有效理论/物理诠释）

| 命题 | 当前状态 | 层级 |
|------|---------|------|
| θ ≈ Ω_m（与观测偏差 ~1%） | ⚠️ 经验锚点 | W2/W3 |
| Regge → 爱因斯坦-希尔伯特收敛性 | ⚠️ 框架完整，证明待填充 | W2 |
| SU(3)×SU(2)×U(1) 完整李代数 | ⚠️ 仅 su(3) Cartan | W2/W3 |

---

## 📁 项目结构

```
CSQIT/
├── Core/                              # 核心模块
│   ├── Axioms.lean                   # 公理体系 A-J 定义
│   ├── TwoAspectTheorems.lean        # 两面性二一定理
│   ├── Consistency.lean              # 一致性证明
│   ├── B_V_Naturalness.lean          # Fin 7 与 θ 推导
│   ├── DarkUniverse.lean             # 暗宇宙分类
│   ├── ScaleDynamics.lean            # 尺度动力学与统一作用量
│   ├── AlgebraicCausality.lean       # 代数因果序
│   ├── ThermodynamicArrow.lean       # 时间箭头
│   ├── QuantumMeasurement.lean       # 量子测量
│   ├── Models/                       # 模型目录
│   │   ├── EnhancedModels.lean       # 增强模型（fin7Model, fin8Model）
│   │   └── FiniteWeavingExamples.lean# 层级编织实例
│   ├── OpenProblems.lean             # 开放问题
│   └── README.lean                   # 模块说明
├── Appendices/                       # 附录模块
├── FutureWork/                       # 未来工作探索
├── lakefile.lean                      # Lake 项目配置
├── lean-toolchain                     # Lean 版本锁定
├── LICENSE.txt                        # MIT 许可证
├── .gitignore                         # Git 忽略规则
└── README.md                          # 本文件
```

---

## ✅ 核心公理体系（A-J）

| 公理 | 描述 | 状态 |
|------|------|------|
| **AxiomA** | 关系元与规则的定义 | ✅ 完备 |
| **AxiomB** | 因果偏序 | ✅ 完备 |
| **AxiomC** | 量子振幅（复数幺正表示） | ✅ 完备 |
| **AxiomD** | 操作编织 | ⚠️ 与 AxiomC 有 trade-off |
| **AxiomJ** | 动力学演化 | ✅ 自洽 |
| **AxiomF–I** | 连续极限、量子引力耦合、规范群、信息因果性 | ⚠️ 框架定义，实例退化 |

---

## 🔧 编译方法

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
# 预期输出：2069 jobs, 0 errors
```

---

## 📊 经验锚点

在两面性诠释下，从公理体系推导出的特征常数：

$$\theta = \frac{1}{2 + 2\cos(2\pi/7)} \approx 0.308$$

与 Planck 2018 观测值 $\Omega_m = 0.311$ 的偏差约 1%。这是从纯公理到可观测数值的完整演绎链（零自由参数），作为经验锚点表明该框架可能与真实物理有关。

---

## ⚠️ 诚实边界声明

1. **所有定理均证明于有限类型**（Fin n, Unit, Bool）
2. **"θ = Ω_m" 是物理解释**（W2/W3），而非数学定理（W1）
3. **连续极限收敛性是开放问题**
4. **不声称已统一量子力学和广义相对论**

---

## 📜 版本演进

| 日期 | 版本 | 主要改进 |
|:---|:---|:---|
| 2026-06-19 | 10.4.5 | 初始版本 |
| 2026-06-22 | 10.5 | W1/W2/W3 分层 |
| 2026-06-28 | 11.0.0 | 因果格、量子测量、时间箭头 |
| 2026-07-01 | 11.1.0 | Fin 7 θ 推导 |
| 2026-07-03 | 11.2.0 | 尺度动力学、代数因果序、2069 jobs 通过 |

---

## 📄 许可证

MIT License

---

*CSQIT v11.2.0 — 因果结构量子信息理论*
*Lean 4 v4.29.0-rc6 — 2069 编译任务，0 错误*
