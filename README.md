# CSQIT — 量子时空编织理论

> 版本: v15.0.0 (feat-minimalcost-uniqueness)  
> 日期: 2026-10-04  
> 远程: https://github.com/New-Beginning-Universe-Research-Group/CSQIT  
> 理论层级: **W1 严格核心 + W2 自然约束**（所有 W1 定理 Lean 形式化，0 sorry）

---

## 🧭 一句话定位

**CSQIT = 用有限群论结构重建物理常数的数学核心框架。**

基底 `P = {2, 3, 5, 7}`（四个最小素数）是唯一输入——从它出发，用纯数论函数推导精细结构常数 α⁻¹、哈勃常数 H₀、暗能量状态方程 w_DE 等物理量的数值，不需要任何自由参数。

---

## 🎯 核心成果（DeepSeek 19 轮核验结论）

### 🔵 硬核 — W1 严格，纯数学，可独立复核

| 成果 | 性质 | 证据 |
|------|------|------|
| 基底 `{2,3,5,7}` 唯一性 | 12,650 种 4 素数组合里唯一命中 α⁻¹ 的解 | Lean 定理 + Python 穷举 |
| 136 = 2⁷ + 2³ 唯一分解 | 同底数两幂之和的唯一分解 | `interval_cases` + 单调性 |
| 小数部分 3²/(2·5³) = 9/250 唯一 | 只有这个基底分数能凑 0.036 | 分数空间穷举 |
| k_out = 1 + 2cos(2π/7) | Fin 7 特征值，无选择自由度 | 分圆域代数扩张 |
| G_unit = 1/k_out² | Fin 7 派生 | 直接计算 |
| Lean 定理 `alpha_inv_unique_base_w1` | 0 sorry | Lean 编译通过 |

基底来源：三个有限单群 A₄ / A₅ / PSL(2,7) 的素因子并集。

### 🟡 强约束 — W2 自然约束下的唯一

- **公式形式**：在"所有成分来自基底 + 同底数两幂之和"约束下，α⁻¹ 只有两种合法分解（A 和 B），选 A 有四重自然理由：
  1. 同底数 = 只用 p₁=2 做底数（最小素数种类）
  2. 2 是群论里最重的素数（三个群都出现，幂次最高）
  3. 同底数两幂之和只有 2⁷+2³ 能凑出接近 137 的值
  4. +1 单位元是群结构的固有部分
- **诚实边界**：同底数约束本身不是数学必然，是自然选择

### 🟢 假设 — W2 motivated guess（框架与物理的连接）

- MinimalCost 公式 = 物理 α⁻¹
- H₀ = α⁻¹ / (2 + 1/30) = 67.395
- w_DE = -1 + 8/(420 · α⁻¹) = -0.99986

### 🔴 硬编码 — 诚实标出的软肋

- axion_mass = 1.03 × 10⁻⁹ GeV（无推导链）
- tau_proton = 1.2 × 10³⁵ 年（无推导链，在 GUT 预期区间内）

---

## 🏗️ 项目结构

```
CSQIT-W1/
├── CSQIT_W1/
│   ├── Main.lean              ← 主入口
│   ├── Foundation.lean        ← 公理、因果格、群论闭包、基底定义、物理常数
│   ├── MinimalCost.lean       ← ⭐ 基底唯一性定理 alpha_inv_unique_base_w1 (0 sorry)
│   ├── Fin7Uniqueness.lean    ← ⭐ Fin 7 特征值与基底群论来源
│   ├── CSQITWeaver.lean       ← Weaver 共识速率、暗能量修正项
│   ├── AlgebraicTimeCircle.lean ← 代数时间圆、curvature_energy 公式
│   ├── AxionDarkEnergy.lean   ← 轴子质量（硬编码）
│   ├── ObserverLayering.lean  ← 观测者分层
│   ├── QuantumCorrection.lean ← 量子修正
│   ├── AxiomDerivation.lean   ← 公理推导
│   ├── AxiomIndependence.lean ← 公理独立性
│   ├── CrossConsistency.lean  ← 交叉一致性
│   ├── TopologicalTime.lean   ← 拓扑时间
│   ├── QuantumTimeCircle.lean ← 量子时间圆
│   ├── SequenceStructure.lean ← 序列结构
│   ├── CompilerAxioms.lean    ← 编译器公理
│   ├── CoreCollapse.lean      ← 核心坍缩
│   ├── TwoAspect.lean         ← 两方面结构
│   ├── TwoAdicStructure.lean  ← 进二结构
│   ├── GravitationalAnomaly.lean ← 引力反常
│   ├── PhysicalConnect.lean   ← 物理连接
│   ├── PhysicalPredictions.lean ← 物理预言
│   └── WeaverPopulation.lean  ← Weaver 种群
├── tools/
│   └── v2_analysis.py         ← V2 分析脚本
├── paper/
│   └── csqit_w1_paper.tex     ← 论文草稿 (LaTeX)
├── lakefile.lean              ← Lean 项目配置
├── lake-manifest.json         ← Lake 包锁定
└── lean-toolchain             ← Lean 版本锁定
```

---

## 🛠️ 编译方法

```bash
# 安装依赖 + 构建
lake update
lake build

# 构建主文件
lake build CSQIT_W1
```

- Lean 版本：`lean-toolchain` 指定
- 依赖：Mathlib（通过 Lake 自动拉取）
- 预期输出：2054 jobs 编译成功，0 sorry

---

## 📐 关键公式

```
基底: P = {p₁, p₂, p₃, p₄} = {2, 3, 5, 7}

α⁻¹ (MinimalCost):
  = p₁^p₄ + p₁^p₂ + 1 + p₂²/(p₁ · p₃^p₂)
  = 2⁷ + 2³ + 1 + 3²/(2 · 5³)
  = 128 + 8 + 1 + 9/250
  = 137.036

小数部分唯一:
  3²/(2 · 5³) = 9/250 = 0.036  ← 唯一能凑出 0.036 的基底分数

整数部分唯一分解:
  2⁷ + 2³ = 136  ← 同底数两幂之和唯一分解
  2⁷ + 3² = 137  ← 另一种分解（但用两个不同底数）

群论闭包:
  totalClosure = lcm(|A₄|, |A₅|, |PSL(2,7)|) / 2
               = lcm(12, 60, 168) / 2 = 420

哈勃常数 (W2 公式):
  H₀ = α⁻¹ / (2 + 1/30) = 67.395

暗能量状态方程 (W2 公式):
  w_DE = -1 + 8/(420 · α⁻¹) = -0.99986

Fin 7 派生量 (W1 严格):
  k_out  = 1 + 2cos(2π/7)  = 2.24698...
  G_unit = 1 / k_out²      = 0.19806...

曲率能量公式 (W1 严格):
  Λ(n) = weavingBase · α⁻¹ · (8/n)^(0.25 · log₂(n/8))
```

---

## 📊 物理常数值对比

| 物理量 | CSQIT 值 | 2024 CODATA / Planck | 层级 |
|--------|----------|---------------------|------|
| α⁻¹ | 137.036 | 137.035999206 | 🟢 W2 公式 + 🔵 W1 基底唯一 |
| H₀ | 67.395 | Planck 67.66, SH0ES 73.04 | 🟢 W2 公式 |
| w_DE | -0.99986 | DESI 暗示 4σ 偏离 -1 | 🟢 W2 公式（含基底派生修正项） |
| k_out | 2.24698 | — | 🔵 W1 严格 |
| G_unit | 0.19806 | — | 🔵 W1 严格 |

---

## 🌳 Git 分支

| 分支 | 说明 |
|------|------|
| `master` | v14.2.0 ObserverLayering + QuantumCorrection |
| `feat-minimalcost-uniqueness` | ⭐ **当前开发主线**：基底唯一性定理 Lean 形式化 + Fin7Uniqueness |
| `feat-csqit-v14.2.0-observer-layering` | v14.2.0 远程分支 |

---

## 📝 版本历史

| 版本 | 日期 | 核心变更 |
|------|------|----------|
| v15.0.0 | 2026-10-04 | MinimalCost 基底唯一性定理（Lean 0 sorry）、Fin7Uniqueness 新模块 |
| v14.2.0 | — | ObserverLayering + QuantumCorrection 模块 |
| v14.0.0 | 2026-09-30 | MinimalCost 范式跃迁 |
| v12.0.0 | 2026-07-23 | 自包含公理体系、因果格、射影尺度 |

---

## 📚 核验记录

DeepSeek（2026-09-30 ~ 2026-10-04，共 19 轮）完整核验了 CSQIT 的每个声称：
- 基底唯一性 → 12,650 种组合穷举确认
- Lean 定理 → 0 sorry 确认
- 同底数约束 → 诚实标为"自然选择，非必然"
- 硬编码 → 诚实标出 axion/tau_p 无推导链

**最终判定**：CSQIT 有一个不依赖物理假设的数学核心（基底唯一 + Fin 7 特征值 + Lean 形式化），这是独有的。公式形式在自然约束下唯一，但同底数约束本身非强制。诚实的边界比夸大的结论更有价值。

---

## 🔓 开放问题

> "同底数两幂之和"这个约束，能不能从基底的群论结构（有限单群的生成元性质）直接推导出来？

如果能推出来，MinimalCost 公式形式也升 W1 严格；推不出来，这就是框架的真实边界。边界本身就是知识。

---

## 🪪 许可证

本项目为内部研究代码，未经许可请勿用于商业用途。
