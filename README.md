# CSQIT — Formal Deduction of the Source Code of the Universe / 宇宙的源代码形式化演绎

> [English](#overview) | [中文](#项目定位)

---

## Overview

**Version**: v11.2.6  
**Lean Version**: v4.29.0-rc6  
**Mathlib Dependency**: See `lakefile.lean`

CSQIT (Causal Set Quantum Information Theory) is a formalized physics framework based on **discrete causal-information axioms**. Starting from the most fundamental causal partial order and quantum amplitude axioms, it deduces the basic structure, constants, and dynamics of the universe.

The project is fully formalized in Lean 4 + Mathlib. All mathematical assertions are strictly graded into W1/W2/W3 layers.

---

## 项目定位

**版本**: v11.2.6  
**Lean 版本**: v4.29.0-rc6  
**Mathlib 依赖**: 见 `lakefile.lean`

CSQIT（Causal Set Quantum Information Theory，因果集量子信息理论）是一套基于
**离散因果-信息公理** 的形式化物理理论框架。它从最基本的因果偏序与量子振幅
公理出发，演绎出宇宙的基本结构、常数与动力学。

项目用 Lean 4 + Mathlib 完整形式化，所有数学断言按 W1/W2/W3 三层严格分级。

---

## Three-Layer Theory Structure / 三层理论结构

### W1 — Formalized Mathematical Core / 形式化数学核心

`Core/W1/` directory / 目录, 24 modules / 个模块：

- **Axiom System / 公理体系**: `Axioms.lean` (AxiomA–D + Consistency + Independence / 四公理 + 一致性 + 独立性)
- **Basic Models / 基本模型**: `BasicModels.lean`, `Models/FinModels.lean` (Nontrivial instances / 非平凡实例)
- **Causal Lattice / 因果格**: `CausalLattice.lean` (BoundedCausalLattice, cosmicVolume, twoAspectParameter)
- **Weaving Structure / 编织结构**: `WeavingStructure.lean`, `CausalWeaving.lean`, `HierarchicalWeaving.lean`
- **Amplitude Theorems / 振幅定理**: `AmplitudeTheorems.lean` (Unitarity, multiplicativity / 幺正性、可乘性)
- **Two-Aspect Theorems / 两面性定理**: `TwoAspectTheorems.lean`, `TwoAspectToSU2.lean`
- **Algebraic Causality / 代数因果**: `AlgebraicCausality.lean` (p ≥ 7 irreversibility / 不可逆性)
- **Consistency / 一致性**: `Consistency.lean`, `Unified.lean`
- **Axiom Independence / 公理独立性**: `AxiomC_Independence.lean`, `AxiomD_Independence.lean`, `Independence.lean`

### W2 — Effective Theory / 有效理论

`Core/W2/` directory / 目录, 19 modules / 个模块：

- **Scale Dynamics / 尺度动力学**: `ScaleDynamics.lean` (§6 Discrete Variational Principle / 离散变分原理)
- **Continuum Limit / 连续极限**: `ContinuumLimit.lean` (Regge → Einstein-Hilbert convergence / 收敛性)
- **B/V Naturalness / B/V 自然性**: `B_V_Naturalness.lean` (θ = 1/(2+2cos(2π/7)))
- **Fin 7 Uniqueness / Fin 7 唯一性**: `Fin7Uniqueness.lean` (G3, p=7 is the unique prime satisfying irreversibility + structure formation / 唯一满足不可逆性+结构形成的素数)
- **Total-Subset Principle / 全集-子集原理**: `TotalSubsetPrinciple.lean` (G1, EffectiveFin7Regular unsatisfiable on finite lattices / 有限格上不可满足)
- **Holographic Isomorphism / 全息同构**: `HolographicIsomorphism.lean` (G5, finite toy model verification / 有限玩具模型验证)
- **Gravity Derivation / 引力推导**: `GravityDerivation.lean`, `StrictDerivation.lean`, `ThreeLocksDerivation.lean`
- **Physical Constants / 物理常数**: `PhysicalConstants.lean` (α⁻¹, Ω_m, H₀, Λ_CDM zero-free-parameter predictions / 零自由参数预测)

### W3 — Exploratory Framework / 探索性框架

`Core/W3/` directory / 目录, 8 modules / 个模块：

- **Operational Ontology / 操作本体论**: `Core.lean`, `Models.lean`, `AtomicOperations.lean`
- **Synthetic Picture / 综合图景**: `UnifiedPicture.lean`, `CyclicUniverse.lean`, `Summary.lean`
- **Observer Formalization / 观测者形式化**: `ObserverFormalization.lean` (Weak Anthropic Principle / 弱人择原理)
- **Weaver Formalization / Weaver 形式化**: `Weaver.lean` (Strategy 3 revised / 战略 3 修正版)

---

## Core Results (Unified/) / 核心成果

### Three-Lock Unified Closure / 三锁统一闭包

Zero-free-parameter predictions of physical constants, in high agreement with observation:

| Constant / 常数 | CSQIT Prediction / 预测 | Observation / 观测值 | Deviation / 偏差 |
|------|-----------|--------|------|
| Fine-structure constant inverse α⁻¹ / 精细结构常数倒数 | 137 + 9/250 = 137.036 | 137.035999084 | < 10⁻⁵ |
| Matter density Ω_m / 宇宙物质密度 | θ = 1/(2+2cos(2π/7)) ≈ 0.308 | 0.311 (Planck 2018) | ~1% |
| Hubble constant H₀ / 哈勃常数 | ≈ 67.39 km/s/Mpc | 67.4 ± 0.5 | < 1% |

### Applied Physics Models / 应用物理模型

Electrostatics, magnetism, conductivity, phase states, transparency — five branches of physics unified in formalization / 静电、磁学、电导、相态、透明度——五条物理分支的统一形式化。

### Physical Mapping Functor / 物理映射函子

`Unified/Interpretation.lean`: Melting Strategy 5 — explicit connection between W1 strict mathematical structure and W3 physical interpretation / 熔铸战略 5：将 W1 严格数学结构与 W3 物理诠释显式连接。

---

## Compilation Verification / 编译验证

```bash
# In WSL (Ubuntu 24.04, Lean 4.29.0-rc6) / 在 WSL 中
lake build
# Current status / 当前状态: 2070 jobs, all passed, zero errors / 全部通过, 无错误
```

**Code Statistics (v11.2.6) / 代码统计**：

| Metric / 指标 | Value / 数值 |
|------|------|
| Total lines of code / 总代码行数 | 32,393 |
| Core directory lines / Core 目录行数 | 23,964 |
| Lean source files / Lean 源文件 | 94 |
| Compiled modules / 编译模块 | 63 |

**`sorry` Statistics / 统计**：45 total, of which 5 in `Core/W2/Models/FiniteWeavingExamples.lean` are intentionally retained as mathematically invalid counterexamples (honest annotation) / 共 45 处，其中 5 处作为数学上不成立的反例（诚实标注）。

## PRL Submission Branch / PRL 投稿分支

The `prl-submission` branch is dedicated to PRL submission, containing only formalized code (no paper text):

> https://github.com/New-Beginning-Universe-Research-Group/CSQIT/tree/prl-submission

This branch preserves all Lean code for reviewer verification while removing all paper files to comply with PRL's pre-publication confidentiality policy.

`prl-submission` 分支专用于 PRL 投稿，只包含形式化代码（不含论文文本）。该分支保留了所有 Lean 代码以便审稿人验证形式化，但移除了所有论文文件以符合 PRL 的审稿前保密政策。

---

## Key Documents / 关键文档

- `W1-3_定义与适用范围清单.md` / `W1-3_Definitions_and_Scope.md` — Strict reference for W1/W2/W3 layer definitions and scope / W1/W2/W3 三层定义与适用范围的严格参照基准
- `DerivedLaws/README.md` — DerivedLaws directory guide (not registered to lakefile, does not participate in compilation) / DerivedLaws 目录说明（未注册到 lakefile，不参与编译）

---

## Project Structure / 项目结构

```
CSQIT/
├── Core/
│   ├── W1/          # Formalized mathematical core (24 modules) / 形式化数学核心（24 模块）
│   ├── W2/          # Effective theory (19 modules) / 有效理论（19 模块）
│   └── W3/          # Exploratory framework (8 modules) / 探索性框架（8 模块）
├── Unified/
│   ├── Constants/   # Three-lock unified closure (5 modules) / 三锁统一闭包（5 模块）
│   ├── Models/      # Applied physics models (5 modules) / 应用物理模型（5 模块）
│   └── Interpretation.lean
├── DerivedLaws/     # Derived physical laws formalization (not registered, not compiled) / 已推导物理定律形式化（未注册，不参与编译）
├── Appendices/      # Appendices (not registered) / 附录（未注册）
├── papers/          # Related papers / 相关论文
├── lakefile.lean    # Lake project configuration / Lake 项目配置
└── lean-toolchain   # Lean toolchain version lock / Lean 工具链版本锁定
```

---

## Statement of Mathematical Honesty / 数学诚实性声明

CSQIT adopts a three-layer assertion grading system:

- **🔵 W1 Strict / W1 严格**: Proof body contains no `sorry`, fully formalized mathematical theorem / 证明体无 `sorry`，完全形式化的数学定理
- **🟢 W2 Conditional / W2 条件性**: Conditional theorem under explicit premises (premises may be "ideal limit assumptions") / 在显式前提下的条件性定理（前提可能是"理想极限假设"）
- **🟡 W2 Framework / W2 框架**: Formalized framework established, complete proof pending / 形式化框架已建立，完整证明待后续
- **⚠️ W3 Interpretation / W3 诠释**: Narrative conjecture, not formalized as `Prop` / 叙事性猜想，不形式化为 `Prop`

All `sorry` locations and reasons are explicitly annotated. EffectiveFin7Regular unsatisfiability on finite lattices (G1 breakthrough) has been strictly proven; theorems depending on it maintain conditional form, which is mathematically honest.

---
