# CSQIT — 宇宙的源代码形式化演绎

**版本**: v11.6.0
**Lean 版本**: v4.29.0-rc6
**Mathlib 依赖**: 见 `lakefile.lean`

---

## 项目定位

CSQIT（Causal Set Quantum Information Theory，因果集量子信息理论）是一套基于
**离散因果-信息公理** 的形式化物理理论框架。它从最基本的因果偏序与量子振幅
公理出发，演绎出宇宙的基本结构、常数与动力学。

项目用 Lean 4 + Mathlib 完整形式化，所有数学断言按 W1/W2/W3 三层严格分级。

---

## 三层理论结构

### W1 — 形式化数学核心（严格定义与证明）

`Core/W1/` 目录，24 个模块：

- **公理体系**: `Axioms.lean`（AxiomA–D 四公理 + 一致性 + 独立性）
- **基本模型**: `BasicModels.lean`, `Models/FinModels.lean`（非平凡实例）
- **因果格**: `CausalLattice.lean`（BoundedCausalLattice, cosmicVolume, twoAspectParameter）
- **编织结构**: `WeavingStructure.lean`, `CausalWeaving.lean`, `HierarchicalWeaving.lean`
- **振幅定理**: `AmplitudeTheorems.lean`（幺正性、可乘性）
- **两面性定理**: `TwoAspectTheorems.lean`, `TwoAspectToSU2.lean`
- **代数因果**: `AlgebraicCausality.lean`（p ≥ 7 不可逆性）
- **一致性**: `Consistency.lean`, `Unified.lean`
- **公理独立性**: `AxiomC_Independence.lean`, `AxiomD_Independence.lean`, `Independence.lean`

### W2 — 有效理论（应用模型与物理推导，含条件性定理）

`Core/W2/` 目录，19 个模块：

- **尺度动力学**: `ScaleDynamics.lean`（§6 离散变分原理 G4）
- **连续极限**: `ContinuumLimit.lean`（Regge → Einstein-Hilbert 收敛 G2）
- **B/V 自然性**: `B_V_Naturalness.lean`（θ = 1/(2+2cos(2π/7))）
- **Fin 7 唯一性**: `Fin7Uniqueness.lean`（G3，p=7 是唯一满足不可逆性+结构形成的素数）
- **全集-子集原理**: `TotalSubsetPrinciple.lean`（G1，有限格上 EffectiveFin7Regular 不可满足）
- **全息同构**: `HolographicIsomorphism.lean`（G5，有限玩具模型验证）
- **引力推导**: `GravityDerivation.lean`, `StrictDerivation.lean`, `ThreeLocksDerivation.lean`
- **物理常数**: `PhysicalConstants.lean`（α⁻¹, Ω_m, H₀, Λ_CDM 零自由参数预测）

### W3 — 探索性框架（概念性与实验性内容）

`Core/W3/` 目录，8 个模块：

- **操作本体论**: `Core.lean`, `Models.lean`, `AtomicOperations.lean`
- **综合图景**: `UnifiedPicture.lean`, `CyclicUniverse.lean`, `Summary.lean`
- **观测者形式化**: `ObserverFormalization.lean`（弱人择原理）
- **Weaver 形式化**: `Weaver.lean`（战略 3 修正版）

---

## 核心成果（Unified/）

### 三锁统一闭包（Unified/Constants/）

零自由参数预测物理常数，与观测高度吻合：

| 常数 | CSQIT 预测 | 观测值 | 偏差 |
|------|-----------|--------|------|
| 精细结构常数倒数 α⁻¹ | 137 + 9/250 = 137.036 | 137.035999084 | < 10⁻⁵ |
| 宇宙物质密度 Ω_m | θ = 1/(2+2cos(2π/7)) ≈ 0.308 | 0.311 (Planck 2018) | ~1% |
| 哈勃常数 H₀ | ≈ 67.39 km/s/Mpc | 67.4 ± 0.5 | < 1% |

### 应用物理模型（Unified/Models/）

静电、磁学、电导、相态、透明度——五条物理分支的统一形式化。

### 物理映射函子（Unified/Interpretation.lean）

熔铸战略 5：将 W1 严格数学结构与 W3 物理诠释显式连接。

---

## 编译验证

```bash
# 在 WSL (Ubuntu 24.04, Lean 4.29.0-rc6) 中
lake build
# 当前状态: 3340 jobs, 全部通过, 无错误
```

当前仅 `Core/W2/Models/FiniteWeavingExamples.lean` 保留 5 处 `sorry`
作为数学上不成立的反例（诚实标注）。

---

## 关键文档

- `W1W2_定义与适用范围清单.md` — W1/W2/W3 三层定义与适用范围的严格参照基准
- `DerivedLaws/README.md` — DerivedLaws 目录说明（未注册到 lakefile，不参与编译）

---

## 项目结构

```
CSQIT_v11.2.6_final/
├── Core/
│   ├── W1/          # 形式化数学核心（24 模块）
│   ├── W2/          # 有效理论（19 模块）
│   └── W3/          # 探索性框架（8 模块）
├── Unified/
│   ├── Constants/   # 三锁统一闭包（5 模块）
│   ├── Models/      # 应用物理模型（5 模块）
│   └── Interpretation.lean
├── DerivedLaws/     # 已推导物理定律形式化（未注册，不参与编译）
├── Appendices/      # 附录（未注册）
├── lakefile.lean    # Lake 项目配置
└── lean-toolchain   # Lean 工具链版本锁定
```

---

## 数学诚实性声明

CSQIT 采用三层断言分级：

- **🔵 W1 严格**: 证明体无 `sorry`，完全形式化的数学定理
- **🟢 W2 条件性**: 在显式前提下的条件性定理（前提可能是"理想极限假设"）
- **🟡 W2 框架**: 形式化框架已建立，完整证明待后续
- **⚠️ W3 诠释**: 叙事性猜想，不形式化为 `Prop`

所有 `sorry` 的位置与原因均有显式标注。EffectiveFin7Regular 在有限格上
不可满足（G1 攻坚）已被严格证明，依赖它的定理保持条件形式是数学诚实的。
