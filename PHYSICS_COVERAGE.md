# 物理解析覆盖率图（有证据版）

> 用途：回答「这套形式化体系**说出来的话**能约束物理宇宙的哪一部分」。
> 不是「理论物理有多少分支、我们占了几个」，而是「在什么层级上，这里的陈述是有内容的、可被物理读出的」。
>
> 口径：`AxiomA` / `AxiomC` 的类型参数 `M`、`C` 是**任意类型**（[Foundation.lean:48](file:///D:/CSQIT-v23-fix/CSQIT_W1/Foundation.lean#L48)、[:66](file:///D:/CSQIT-v23-fix/CSQIT_W1/Foundation.lean#L66)）。
> 因此本层所有定理都是**模型类定理**：它们说「任何满足这些字段的结构都如何」，
> 不说「我们的宇宙如何」。这是本文件全部判断的前提。
>
> 证据口径：每条给定理名 + `文件:行号`；计数类证据给「命中数 / 文件数」，
> 统计范围是本仓库 69 个 `.lean`、20948 行（排除 `.lake`）。

---

## 0. 一句话结论

**这套体系落在「约束层级」，不在「定律层级」。**

它能做的是**排除**：排除某一类过程代数、某一类因果序、某一类自指结构、某一类「数值由公理推出」的说法。
它不能做的是**描述**：没有状态空间、没有叠加、没有 Born 规则、没有 ℏ 的标度、没有度规、没有作用量。
「有效分层为什么存在」在当前语言里**没有可陈述的对象**（§4）。

| 层级 | 内容 | 条数 | 判定 |
|---|---|---|---|
| 一、已能解析 | 真定理支持的排除性约束 | 50 条定理 / 7 组 | 可引，但只能引为「模型类排除」 |
| 二、可能解析 | 需外挂结构或新公设 | 7 类结构缺口（+1 条反向公理） | 目前只有签名、没有内容 |
| 三、不可能解析 | 零命中 + no-go | 39 项零命中 / 9 条 no-go | 缺的是字段，不是工作量 |

---

## 1. 第一层：已能解析（真定理支持）

**判断标准**：任何满足这些公理的模型都必须如此。
**价值**：排除（某某类过程代数不可能存在），不是描述。
**限度**：下面每一条都**不是**关于某个物理系统的陈述，而是关于「模型类」的陈述。
引用时必须写「在任何满足 `AxiomA`/`AxiomC` 的模型里」，不能写「在宇宙里」。

### 1.1 依赖/输入结构必然为空

| 陈述 | 定理 | 位置 | 约束的物理对象类别 | 排除什么 |
|---|---|---|---|---|
| 任何规则的可组合 + 依赖串联 + 无重复依赖 ⇒ 所有规则的输入列表为空 | `core_collapse` | [CompilerAxioms.lean:128](file:///D:/CSQIT-v23-fix/CSQIT_W1/CompilerAxioms.lean#L128) | 「分层依赖 / import 型因果」这一类模型 | 排除「因果分层靠依赖传递实现」 |
| `AxiomA` 版本的同一结论 | `input_must_be_empty` | [CoreCollapse.lean:57](file:///D:/CSQIT-v23-fix/CSQIT_W1/CoreCollapse.lean#L57) | 同上 | 同上 |
| 塔的每一层 `input` 恒为空 | `layer_input_empty` | [Tower.lean:190](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Tower.lean#L190) | 分层结构中的「层间依赖」 | 排除「塔的层携带不同依赖规则」 |
| 塔顶 `input` 恒为空 | `top_input_empty` | [Tower.lean:195](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Tower.lean#L195) | 同上 | 排除「顶层汇总全塔依赖」 |

### 1.2 因果序：不导出、不唯一、无最大元

| 陈述 | 定理 | 位置 | 约束的物理对象类别 | 排除什么 |
|---|---|---|---|---|
| 不存在只依赖五字段的 `ord`，在每个模型上都给出与 `compose` 相容的严格偏序 | `no_uniform_compatible_order` | [OrderAndFixedPoint.lean:73](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/OrderAndFixedPoint.lean#L73) | 全局时间序 | 排除「组合律 + 结合律自动给出时间序」 |
| 若模型无右单位元，则可构造相容严格偏序 | `conditional_order` | [:87](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/OrderAndFixedPoint.lean#L87) | 同上 | 给出唯一可行的构造条件（不是公理后果） |
| 存在方向相反的两条相容序 ⇒ 不存在同时包含二者的反自反传递关系 | `no_maximal_compatible_order` | [OrderMaximality.lean:77](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/OrderMaximality.lean#L77) | 「终极层 / 最大一致序」 | 排除「存在唯一的终极因果序」 |
| 乘积模型上具体存在这样一对相反序 | `pair_two_compatible_orders_opposite` | [:100](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/OrderMaximality.lean#L100) | 同上 | 把上一条从抽象变成可检验实例 |
| 不存在「纯 `AxiomA` ⇒ 可达关系全序」的普遍定理 | `not_universally_total` | [:144](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/OrderMaximality.lean#L144) | 线性时间 | 排除「因果序自动是全序」 |
| 相容序唯一 ⟺ 可达关系全序 | `causal_order_unique_iff_reach_total` | [OrderUniqueness.lean:267](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/OrderUniqueness.lean#L267) | 唯一性判据 | 给出「何时唯一」的充要条件 |
| 有限载体不承载因果-振幅层 | `no_layer_of_fintype` | [CausalLayerSharpening.lean:260](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/CausalLayerSharpening.lean#L260) | 有限模型上的因果层 | 排除「v23 有限主体上架因果层」 |
| 无右作用元强制载体无限 | `no_right_id_implies_infinite` | [:273](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/CausalLayerSharpening.lean#L273) | 载体基数 | 把上一条升级为结构性刻画 |
| `Fin n` 上不存在 `V1CausalAmplitudeLayer` | `fin_no_causal_layer` | [V23Interface.lean:111](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/V23Interface.lean#L111) | v23 主体模型 | 排除「v23 主体承载 V1 因果层」 |
| `Fin n` 上振幅层可实现、因果层不可实现（合取） | `v23Finite_amplitude_without_causality` | [:121](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/V23Interface.lean#L121) | 同上 | 把「有相位 ≠ 有因果层」写成定理 |

### 1.3 自指与自生成：都不是公理后果

| 陈述 | 定理 | 位置 | 约束的物理对象类别 | 排除什么 |
|---|---|---|---|---|
| `AxiomA` 不保证自指不动点存在 | `no_uniform_fixed_point` | [OrderAndFixedPoint.lean:160](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/OrderAndFixedPoint.lean#L160) | 「宇宙 = 自指不动点」 | 排除「自指闭合可由公理推出」 |
| 不动点在另一个合法模型中成立 | `fixed_point_exists_in_some_model` | [:169](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/OrderAndFixedPoint.lean#L169) | 同上 | 说明这是模型性质，不是定理 |
| 见证塔顶没有不动点 | `witnessTower_top_no_fixed_point` | [Top.lean:62](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Top.lean#L62) | 塔顶 | 同上，具体到塔 |
| 不存在自生成满射 `Φ : C → (C → C)` | `no_surjective_self_pi` | [OperadImpossibility.lean:172](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/OperadImpossibility.lean#L172) | 「操作作用于自身且满射」 | 排除这一整类自生成语义 |
| `AxiomA` 模型上的同一条 | `no_surjective_self_map_of_axiomA` | [:193](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/OperadImpossibility.lean#L193) | 同上 | 同上 |
| 见证塔顶不存在自生成满射 | `witnessTower_top_no_self_generation` | [Top.lean:73](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Top.lean#L73) | 塔顶 | 同上，具体到塔 |

### 1.4 振幅层：刚性（组合没有独立自由度）

这一组不是「排除」，而是**结构约束**：组合层不是独立于振幅层的自由度。

| 陈述 | 定理 | 位置 |
|---|---|---|
| `compose x y = compose x' y'` ⟺ `amp x * amp y = amp x' * amp y'` | `compose_eq_iff_amplitude_mul` | [AmplitudeRigidity.lean:67](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/AmplitudeRigidity.lean#L67) |
| 给定振幅乘积，组合元素被唯一钉死 | `compose_forced_by_amplitude` | [:83](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/AmplitudeRigidity.lean#L83) |
| 同载体上两个结构，振幅相同 ⇒ `compose` 相同 | `compose_eq_of_same_amplitude` | [:98](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/AmplitudeRigidity.lean#L98) |
| 振幅相同 ⇒ 单步可达关系相同 | `oneStepReach_eq_of_same_amplitude` | [:112](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/AmplitudeRigidity.lean#L112) |
| `x∘y = x` ⟺ `amp y = 1` | `compose_eq_left_iff_amplitude_eq_one` | [:137](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/AmplitudeRigidity.lean#L137) |
| 存在相容严格序 ⟺ `1 ∉ range(amplitude)` | `exists_compatible_order_iff_amplitude_ne_one` | [:161](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/AmplitudeRigidity.lean#L161) |

### 1.5 数值：不是五字段的函数（`no_determiner` 家族）

这一组排除的是「某个数从公理结构里推出来了」这类说法。

| 陈述 | 定理 | 位置 |
|---|---|---|
| 通用判据：同字段、异值 ⇒ 不存在决定函数 | `no_determiner` | [IndependenceCheck.lean:209](file:///D:/CSQIT-v23-fix/CSQIT_W1/IndependenceCheck.lean#L209) |
| 闭包值 420 不是五字段的函数 | `closure_not_determined_by_fields` | [:233](file:///D:/CSQIT-v23-fix/CSQIT_W1/IndependenceCheck.lean#L233) |
| 群阶 12 不是五字段的函数 | `order12_not_determined_by_fields` | [:249](file:///D:/CSQIT-v23-fix/CSQIT_W1/IndependenceCheck.lean#L249) |
| 群阶 60 不是五字段的函数 | `order60_not_determined_by_fields` | [:259](file:///D:/CSQIT-v23-fix/CSQIT_W1/IndependenceCheck.lean#L259) |
| 群阶 168 不是五字段的函数 | `order168_not_determined_by_fields` | [:269](file:///D:/CSQIT-v23-fix/CSQIT_W1/IndependenceCheck.lean#L269) |
| H₀ 的 30/61 不是五字段的函数 | `hubble_not_determined_by_fields` | [:441](file:///D:/CSQIT-v23-fix/CSQIT_W1/IndependenceCheck.lean#L441) |
| 换基后 `e1² - e3 ≠ 42` | `identity_42_fails_on_altBase` | [:484](file:///D:/CSQIT-v23-fix/CSQIT_W1/IndependenceCheck.lean#L484) |
| 韦达配对：另一根仍是解 | `vieta_partner` | [:726](file:///D:/CSQIT-v23-fix/CSQIT_W1/IndependenceCheck.lean#L726) |
| 12 以内全部解（21 组，非唯一） | `solsUpTo_12_eq` | [:790](file:///D:/CSQIT-v23-fix/CSQIT_W1/IndependenceCheck.lean#L790) |
| 素解字典序最小 ≠ 唯一 | `prime_solution_lex_min` | [:1200](file:///D:/CSQIT-v23-fix/CSQIT_W1/IndependenceCheck.lean#L1200) |
| 不存在无限分解链 | `no_infinite_decomposition` | [:1349](file:///D:/CSQIT-v23-fix/CSQIT_W1/IndependenceCheck.lean#L1349) |

### 1.6 能量/粗粒化/流：四条方向性事实

| 陈述 | 定理 | 位置 | 约束的物理对象类别 |
|---|---|---|---|
| `curvature_energy` 不是全定义域严格递减（反例 1 < 8） | `curvature_energy_not_strict_decreasing` | [CurvatureEnergyRefutation.lean:75](file:///D:/CSQIT-v23-fix/CSQIT_W1/CurvatureEnergyRefutation.lean#L75) | 「能标随 n 单调下降」 |
| 具体反例：`∃ a b, a < b ∧ ce a < ce b` | `curvature_energy_counterexample` | [:88](file:///D:/CSQIT-v23-fix/CSQIT_W1/CurvatureEnergyRefutation.lean#L88) | 同上 |
| 非单射粗粒化 ⇒ 不存在守恒源振幅的目标振幅 | `no_amplitude_factorization_of_not_injective` | [Cuts.lean:235](file:///D:/CSQIT-v23-fix/CSQIT_LayerCuts/Cuts.lean#L235) | 「降维不改变振幅标签」 |
| 振幅沿流是层不变量 ⟺ 初值为 1 | `flowAmplitude_layerInvariant_iff` | [:264](file:///D:/CSQIT-v23-fix/CSQIT_LayerCuts/Cuts.lean#L264) | 「耦合不跑动」 |
| 初值非 1 ⇒ 不是层不变量 | `flowAmplitude_not_layerInvariant` | [:287](file:///D:/CSQIT-v23-fix/CSQIT_LayerCuts/Cuts.lean#L287) | 同上 |
| 模长恒为 1，α 一类量不能从模长读出 | `amplitude_normSq_eq_one` | [:295](file:///D:/CSQIT-v23-fix/CSQIT_LayerCuts/Cuts.lean#L295) | 「α 是模长效应」 |

### 1.7 塔与势：存在性可构造，内容为空

| 陈述 | 定理 | 位置 | 说明 |
|---|---|---|---|
| 塔顶是 `AxiomA + AxiomC` 模型 | `top_model_exists` | [Tower.lean:128](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Tower.lean#L128) | 只证存在性，不证承载序/唯一性/自生成 |
| `top` 是 Set 级并的最小集合 | `top_is_colimit` | [:138](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Tower.lean#L138) | 「余极限」只在 Set 层成立 |
| 层到顶保 `compose` | `layerToTop_compose` | [:163](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Tower.lean#L163) | 层间是嵌入，不是投影 |
| 层内可达单向上行 | `layerToTop_reach` | [:172](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Tower.lean#L172) | 反向不成立 |
| 塔顶无最大相容序 | `pairTower_top_no_maximal_order` | [AxiomCMaximality.lean:119](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/AxiomCMaximality.lean#L119) | 塔顶不是「终极层」 |
| 势值不是 `AxiomA` 字段的函数 | `witness_potential_not_determined_by_fields` | [Potential.lean:192](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Potential.lean#L192) | 任何「引力势被推导出来」的说法与此冲突 |
| 单点模型上一切加性势为零 | `unit_additivePotential_eq_zero` | [:229](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Potential.lean#L229) | 字段从未「给出」非零势 |

**层一小结**：50 条定理、7 组。全部是「模型类排除」。
没有一条能写成「某物理系统会怎样演化」——因为 `AxiomA` 里没有演化，只有组合。

---

## 2. 第二层：可能解析（需外挂结构或新公设）

### 2.1 核心判断：`AxiomC` 的 U(1) 相位离量子力学有多远

已有的（[Foundation.lean:66-74](file:///D:/CSQIT-v23-fix/CSQIT_W1/Foundation.lean#L66)）：

```
amplitude : C → ℂ
norm_one  : ∀ α, normSq (amplitude α) = 1
comp_rule : amplitude (compose α β) = amplitude α * amplitude β
amplitude_injective : Function.Injective amplitude
```

这是一个从组合半群到单位圆的**单射乘法同态**。它确实有相位、有乘性、有单射。

但它离「量子态」差的是**七件结构**，逐件给证据：

| # | 缺的结构 | 证据（实测计数 / 字段缺失） | 补上之后才能陈述什么 |
|---|---|---|---|
| 1 | 复向量空间（状态空间） | `InnerProductSpace` 0 命中、`NormedSpace` 0 命中、`NormedAddCommGroup` 0 命中；`Module` 23 命中但全在 [Cuts.lean:144-205](file:///D:/CSQIT-v23-fix/CSQIT_LayerCuts/Cuts.lean#L144) 用于压缩比维数，不在 `AxiomC` 里 | 「态是某个 `V` 的元素」 |
| 2 | 叠加（加法） | `AxiomA` 七字段（[:48-62](file:///D:/CSQIT-v23-fix/CSQIT_W1/Foundation.lean#L48)）与 `AxiomC` 四字段（[:66-74](file:///D:/CSQIT-v23-fix/CSQIT_W1/Foundation.lean#L66)）中无任何 `+`；振幅是 `C → ℂ` 的函数，不是向量 | 「`α + β` 是态」；干涉项 |
| 3 | Born 规则 | `ProbabilityTheory` 0、`IsProbabilityMeasure` 0、`MeasureTheory` 0；`norm_one` 只是归一化，没有可测空间（注释 [Axioms.lean:831-832](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/Axioms.lean#L831) 称其「保证概率解释一致性」，但签名中无测度对象） | 「测得某值的概率 = \|⟨φ\|ψ⟩\|²」 |
| 4 | ℏ 的标度 | `hbar_interpretation : Prop := True`（[Foundation.lean:1265](file:///D:/CSQIT-v23-fix/CSQIT_W1/Foundation.lean#L1265)）；`speedOfLight_interpretation := True`（[:1273](file:///D:/CSQIT-v23-fix/CSQIT_W1/Foundation.lean#L1273)）；`gravitationalConstant_interpretation := True`（[:1281](file:///D:/CSQIT-v23-fix/CSQIT_W1/Foundation.lean#L1281)） | 「作用量以 ℏ 为单位量子化」；有量纲的 `exp(-iHt/ℏ)` |
| 5 | 复合系统 | `TensorProduct` 0 命中；`AxiomA M C` 对任意 `M,C`，但没有 `AxiomA (M×M) (C×C)` 的桥接定理 | 「两系统并置」；纠缠作为非积态 |
| 6 | 可观测量 | `SelfAdjoint` 0、`IsSelfAdjoint` 0、`Spectrum` 0、`Eigenvalue` 0、`Eigenvector` 0 | 「测量 = 本征值」 |
| 7 | 动力学算子 | `AxiomJ.evolve : C → M → M`（[Axioms.lean:689](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/Axioms.lean#L689)）是「规则作用于关系元」；`Unitary` 2 命中均为 `UnitaryTimeCircle`（[QuantumTimeCircle.lean:147](file:///D:/CSQIT-v23-fix/CSQIT_W1/QuantumTimeCircle.lean#L147)，一个 `[0,2π)` 上的相位圆类型，不是算子）；76 处小写 `unitary` 文本（含 `nonunitary` 子串）集中在 `fin8_nonunitary_amplitude` 否证系列（[EnhancedModels.lean:670](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/EnhancedModels.lean#L670)） | 「态按酉算子演化」 |

**外加一条反向障碍（第 8 件）**：
`amplitude_injective`（[Foundation.lean:74](file:///D:/CSQIT-v23-fix/CSQIT_W1/Foundation.lean#L74)）要求不同规则振幅不同。
而量子态是**射线**，「向量 → 射线」恰恰**不单射**。
所以这条公理与射影化方向相反；要接量子力学，先要放弃或弱化它。这不是「补一个字段」，是「改一条公理」。

**结论**：有「相位标签」，没有「量子态」。
差的是 7 件结构 + 1 条反向公理；不是「再加一个定义」的量级。

### 2.2 补结构后能得到什么，代价是什么

| 补什么 | 能得到什么陈述 | 代价 |
|---|---|---|
| 复 Hilbert 空间 + 内积 | 「振幅是内积」`amp α = ⟨φ, ψ_α⟩` | 新公设；`C` 必须嵌入某 `V`，与 `amplitude_injective` 冲突 |
| 加法 + 完备化 | 叠加、干涉 | 新公设；`compose` 与 `+` 的相容性（分配律）需要另行假定 |
| 测度 + Born 规则 | 概率预言 | 新公设；且需要「测量」这个当前不存在的对象 |
| 作用量量纲 + ℏ | 真正的动力学 | 新公设；当前 `ℏ` 是 `True` |
| 张量积 | 复合系统、纠缠 | 新公设；`AxiomA` 无积构造 |
| 自伴算子谱 | 可观测量 | 新公设；依赖 §2.1 的第 1、2 件 |

### 2.3 三大结构性解耦（仓库自己认定的事实）

[Axioms.lean:728-745](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/Axioms.lean#L728) 明确写出三条，并在 [:781-782](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/Axioms.lean#L781) 标注「都发生在 W1 层——它们是数学事实，不是诠释问题」：

1. **output 与 compose 不对称**：`compose_output` 丢弃前件的 output（[:60](file:///D:/CSQIT-v23-fix/CSQIT_W1/Foundation.lean#L60)），故在左可迁结构下 output 必为常函数。
2. **amplitude 与 lt 解耦**：没有公理把 `amplitude : C → ℂ` 与 `lt : M → M → Prop` 联系起来（[:734-737](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/Axioms.lean#L734)）。
3. **entropy 与 amplitude 解耦**：`entropy` 与 `amplitude` 之间没有约束（[:739-742](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/Axioms.lean#L739)）。

含义：即使补上 §2.1 的结构，这三条解耦也不会自动消失；
「相位 + 因果 + 熵」目前是**三个独立装饰**，不是一个有机整体。

### 2.4 扩展公理 F–K：有签名，无内容

| 公理 | 字段 | 唯一模型 | 判定 |
|---|---|---|---|
| `AxiomF`（连续极限） | `scale : ℕ → ℝ`，`scale_pos`，`scale_limit`（相邻差 → 0） | `scale := fun _ => 1`（[EnhancedModels.lean:426](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/EnhancedModels.lean#L426)） | 只是一个收敛序列，不是粗粒化映射 |
| `AxiomG`（自旋网络） | `spin_network : Type`，`amplitude_spin : spin_network → ℂ` | `spin_network := Unit`，`amplitude_spin := 1`（[:435-436](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/EnhancedModels.lean#L435)） | 类型无结构、无图、无自旋标签 |
| `AxiomH`（规范场） | `gauge_group : Type`，`field_content`，`lagrangian` | `gauge_group := Unit`，`field_content := 0`，`lagrangian := 0`（[:438-441](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/EnhancedModels.lean#L438)） | 规范群平凡、作用量恒零 |
| `AxiomJ`（动力学） | `evolve : C → M → M`，`causal_update`，`comp_evolve` | 仓库自述「无非平凡实例」（[Axioms.lean:809](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/Axioms.lean#L809)） | 无演化内容 |
| `AxiomK`（永恒此刻） | `eternal_now_principle`、`time_as_relation`（强制全序）、`holographic_principle` | `fin7AxiomK` / `fin8AxiomK`（[EnhancedModels.lean:1120](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/EnhancedModels.lean#L1120)、[:1132](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/EnhancedModels.lean#L1132)） | 唯一「推论」是字段投影（[Axioms.lean:1035](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/Axioms.lean#L1035)） |

注意 `AxiomD.op_weaving` 同样退化：[Axioms.lean:449-450](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/Axioms.lean#L449) 自述「在所有已知标准 Theory 模型中，前提 `lt(output α)(output β)` 恒为 False」。

### 2.5 能补到哪一步的现实路径

| 目标 | 最小补法 | 会得到的定理（可预期形式） | 不会得到的 |
|---|---|---|---|
| 「振幅是内积」 | `V` + 内积 + `amp` 因子化 | `amp α = ⟨φ, ψ_α⟩` 型引理 | Born 概率（缺测度） |
| 「层间粗粒化必改振幅」 | 已有 `no_amplitude_factorization_of_not_injective`（[Cuts.lean:235](file:///D:/CSQIT-v23-fix/CSQIT_LayerCuts/Cuts.lean#L235)） | 已是定理 | 具体跑动方程 |
| 「耦合随层跑动」 | 已有 `flowAmplitude_layerInvariant_iff`（[:264](file:///D:/CSQIT-v23-fix/CSQIT_LayerCuts/Cuts.lean#L264)） | 二分：不变量 ⟺ 初值 1 | 跑动速度、β 函数 |
| 「存在加性势」 | 已有接口 `AdditivePotential`（[Potential.lean:42](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Potential.lean#L42)） | 非零见证（[:175](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Potential.lean#L175)） | 势的具体值（[:192](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Potential.lean#L192) 说不由字段决定） |

---

## 3. 第三层：不可能解析（有否定证据）

### 3.1 零命中（实测计数）

范围：仓库 69 个 `.lean` 文件、20948 行，排除 `.lake`。

| 术语 | 命中 | 文件 |
|---|---|---|
| `Hilbert` | 0 | 0 |
| `DensityMatrix` / `DensityOperator` | 0 / 0 | 0 / 0 |
| `Hamiltonian` | 0 | 0 |
| `PathIntegral` | 0 | 0 |
| `Metric` | 0 | 0 |
| `InnerProductSpace` / `NormedSpace` | 0 / 0 | 0 / 0 |
| `SelfAdjoint` / `IsSelfAdjoint` | 0 / 0 | 0 / 0 |
| `Spectrum` / `Eigenvalue` / `Eigenvector` | 0 / 0 / 0 | 0 / 0 / 0 |
| `TensorProduct` | 0 | 0 |
| `Basis` | 0 | 0 |
| `ProbabilityTheory` / `MeasureTheory` / `IsProbabilityMeasure` | 0 / 0 / 0 | 0 / 0 / 0 |
| `Decoherence` | 0 | 0 |
| `BornRule` | 0 | 0 |
| `Boltzmann` / `PartitionFunction` / `Temperature` | 0 / 0 / 0 | 0 / 0 / 0 |
| `Renormalization` / `Renormalisation` | 0 / 0 | 0 / 0 |
| `EffectiveField` / `EFT` | 0 / 0 | 0 / 0 |
| `Noether` / `SymmetryGroup` | 0 / 0 | 0 / 0 |
| `Lorentz` / `Minkowski` / `Spacetime` | 0 / 0 / 0 | 0 / 0 / 0 |
| `Graviton` / `Einstein` / `Geodesic` | 0 / 0 / 0 | 0 / 0 / 0 |
| `Riemann` / `Manifold` / `FiberBundle` | 0 / 0 / 0 | 0 / 0 / 0 |
| `Superposition` | 0 | 0 |

非零但需解释的四项（全部是命名巧合或退化见证）：

| 术语 | 命中 | 文件 | 实际是什么 |
|---|---|---|---|
| `Curvature` | 81 | 8 | 全部是 `curvature_energy`（[AlgebraicTimeCircle.lean:61](file:///D:/CSQIT-v23-fix/CSQIT_W1/AlgebraicTimeCircle.lean#L61)）——整数 `n` 上的组合函数，不是黎曼曲率 |
| `Entropy` | 69 | 3 | 全部是 `AxiomI.entropy` 字段与注释（[Axioms.lean:633](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/Axioms.lean#L633)） |
| `Planck` | 67 | 8 | `planckMass`（[Foundation.lean:1104](file:///D:/CSQIT-v23-fix/CSQIT_W1/Foundation.lean#L1104)）与审计行 |
| `Gauge` | 16 | 7 | 全在 `AxiomH` 字段与 `GaugeAndEndo.lean` 文件名；模型取 `Unit`（[EnhancedModels.lean:439](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/EnhancedModels.lean#L439)） |
| `hbar` | 1 | 1 | `hbar_interpretation : Prop := True`（[Foundation.lean:1265](file:///D:/CSQIT-v23-fix/CSQIT_W1/Foundation.lean#L1265)） |

### 3.2 no-go 定理 → 缺的是哪个字段

| no-go | 位置 | 缺的字段/结构 |
|---|---|---|
| `no_uniform_compatible_order` | [OrderAndFixedPoint.lean:73](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/OrderAndFixedPoint.lean#L73) | `AxiomA` 无 `ord` 字段；序不在签名里 |
| `no_maximal_compatible_order` | [OrderMaximality.lean:77](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/OrderMaximality.lean#L77) | 无「序集合的最大元」结构 |
| `not_universally_total` | [:144](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/OrderMaximality.lean#L144) | 无全序字段（`AxiomK.time_as_relation` 是另行添加，见 §2.4） |
| `no_surjective_self_pi` | [OperadImpossibility.lean:172](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/OperadImpossibility.lean#L172) | 无自指编码 `Φ` |
| `no_determiner` | [IndependenceCheck.lean:209](file:///D:/CSQIT-v23-fix/CSQIT_W1/IndependenceCheck.lean#L209) | 数值不以字段形式存在；无「参数 → 字段」的写入机制 |
| `curvature_energy_not_strict_decreasing` | [CurvatureEnergyRefutation.lean:75](file:///D:/CSQIT-v23-fix/CSQIT_W1/CurvatureEnergyRefutation.lean#L75) | 无能量单调性公设；定义域与单调性错位 |
| `closure_not_determined_by_fields` | [IndependenceCheck.lean:233](file:///D:/CSQIT-v23-fix/CSQIT_W1/IndependenceCheck.lean#L233) | 12/60/168 无字段来源 |
| `witness_potential_not_determined_by_fields` | [Potential.lean:192](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Potential.lean#L192) | 无度规字段 |
| `fin_no_causal_layer` | [V23Interface.lean:111](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/V23Interface.lean#L111) | 有限载体缺无限性（`no_right_id_implies_infinite`） |

### 3.3 判定口径

「不可能解析」在这里严格指：**当前签名里没有那个字段**，
而 `no-go` 说明「只靠现有字段无论如何都造不出来」。
它与「还没做」的区别是：前者需要**改公理**，后者只需加定理。

---

## 4. 必答题：这套体系能不能描述「有效的分层」本身

**问题**：为什么自然界可以分成原子/分子/凝聚态/星体这些各自稳定、各自只需少量参数的层级？

### 4.1 当前语言里可陈述的对象（有）

| 对象 | 形式化 | 位置 |
|---|---|---|
| 离散索引与载体子集族 | `RuleTower M C ι` | [Tower.lean:44](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Tower.lean#L44) |
| 每层上的 `AxiomA` / `AxiomC` 限制 | `layerAxiomA` / `layerAxiomC` | [Tower.lean:90-97](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Tower.lean#L90)、[:110-115](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Tower.lean#L110) |
| Set 级并 `top` 与泛性质 | `top_is_colimit` | [:138](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Tower.lean#L138) |
| 整数层级 `n_k = 420/k` 与三角值 | `alpha_level_n = 105`、`alpha_level_angle = π/2` | [ObserverLayering.lean:59-111](file:///D:/CSQIT-v23-fix/CSQIT_W1/ObserverLayering.lean#L59) |
| 尺度序列（相邻差收敛） | `AxiomF.scale : ℕ → ℝ` | [Axioms.lean:555-557](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/Axioms.lean#L555) |

### 4.2 当前语言里没有可陈述对象的四件事（没有）

| 需要的东西 | 现状 | 证据 |
|---|---|---|
| **层的稳定性判据** | 无「稳定」谓词；无谱隙；无能隙 | `Spectrum` 0 命中、`Eigenvalue` 0 命中 |
| **层间有效耦合 / 流方程** | 只有二分：振幅是层不变量 ⟺ 初值 1 | `flowAmplitude_layerInvariant_iff`（[Cuts.lean:264](file:///D:/CSQIT-v23-fix/CSQIT_LayerCuts/Cuts.lean#L264)） |
| **每层只需少量参数** | 数值不由字段决定；参数不在签名里 | `no_determiner`（[IndependenceCheck.lean:209](file:///D:/CSQIT-v23-fix/CSQIT_W1/IndependenceCheck.lean#L209)） |
| **粗粒化映射的范畴** | 只有一条引理，方向是「非单射 ⇒ 必改振幅」 | `no_amplitude_factorization_of_not_injective`（[Cuts.lean:235](file:///D:/CSQIT-v23-fix/CSQIT_LayerCuts/Cuts.lean#L235)） |

### 4.3 结论

**不能。当前语言里没有可陈述的对象。**

理由不是「没做够」，而是三处签名级缺口：

1. **依赖不能分层**：`layer_input_empty`（[Tower.lean:190](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Tower.lean#L190)）与 `top_input_empty`（[:195](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Tower.lean#L195)）说明每一层的输入恒为空。
   「为什么每层只需少量参数」在形式上对应「层间依赖稀疏」，而这里依赖被证成**恒为空**——它是比稀疏更强的结论，强到无法区分不同层。
2. **层只能是载体 + 振幅值**：`top_model_exists`（[:128](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Tower.lean#L128)）只给存在性；
   `layerToTop_reach`（[:172](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Tower.lean#L172)）只给单向上行；`pairTower_top_no_maximal_order`（[AxiomCMaximality.lean:119](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/AxiomCMaximality.lean#L119)）否证「终极层」。
3. **W3 的层级标签是命名，不是推导**：`ObserverLayering.lean:50-53` 把 `n = 8/64/105/420` 标为 QCD/EW/α⁻¹/DE，这是注释里的标签；
   对应定理只证 `105 = p₂p₃p₄`、角度 `= π/2`、`cos = 0`、`sin = 1`（[:63](file:///D:/CSQIT-v23-fix/CSQIT_W1/ObserverLayering.lean#L63)、[:80](file:///D:/CSQIT-v23-fix/CSQIT_W1/ObserverLayering.lean#L80)、[:99](file:///D:/CSQIT-v23-fix/CSQIT_W1/ObserverLayering.lean#L99)、[:108](file:///D:/CSQIT-v23-fix/CSQIT_W1/ObserverLayering.lean#L108)），不证「这一层是 QCD」。

### 4.4 若一定要给一个「最弱可陈述版本」

可以写成两条**否定式**，且必须标明是模型类结论：

1. 「任何满足 `CompilerAxiom` 的分层模型，层间依赖恒为空」——`layer_input_empty`。
2. 「任何有限的因果-振幅层载体都不存在；层要求无限载体」——`no_layer_of_fintype`（[CausalLayerSharpening.lean:260](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/CausalLayerSharpening.lean#L260)）与 `no_right_id_implies_infinite`（[:273](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/CausalLayerSharpening.lean#L273)）。

这两条说的是「分层的代价」，不是「分层为什么有效」。
后者需要的参数化层族、层间投影、稳定性判据，当前一个都没有。

---

## 5. 与物理分支的对读（只列有形式化落点的）

| 物理分支 | 本体系能说什么 | 证据 | 不能说什么 |
|---|---|---|---|
| 量子力学 | 相位标签存在、组合刚性 | `AxiomC`（[Foundation.lean:66](file:///D:/CSQIT-v23-fix/CSQIT_W1/Foundation.lean#L66)）、`compose_forced_by_amplitude` | 态、叠加、Born 规则、ℏ |
| 量子场论 | 无 | `PathIntegral` 0、`EffectiveField` 0 | 任何 |
| 广义相对论 | 无 | `Metric` 0、`Riemann` 0、`Geodesic` 0 | 任何 |
| 统计力学 | 无（`AxiomI.entropy` 只是字段） | `Boltzmann` 0、`PartitionFunction` 0、`Temperature` 0 | 任何 |
| 凝聚态 | 无 | `Basis` 0、`TensorProduct` 0 | 任何 |
| 原子/分子结构 | 壳层容量 2n² 的算术推导 | `shell_capacity_from_quantum_states`（[PeriodicTable.lean:119](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/PeriodicTable.lean#L119)） | 能级交错；该文件自述「实际值与简单壳层容量累加略有不同，后续再加入能级交错修正」（[:97-98](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/PeriodicTable.lean#L97)） |
| 宇宙学 | 三个常数诠释都是 `True` | `hbar_interpretation` / `speedOfLight_interpretation` / `gravitationalConstant_interpretation`（[Foundation.lean:1265/1273/1281](file:///D:/CSQIT-v23-fix/CSQIT_W1/Foundation.lean#L1265)） | 任何数值预言 |

**注意**：`PeriodicTable.lean` 的 `shell_capacity` 是纯算术（∑(2l+1) = n²，再乘自旋简并 2），
它解释的是「2n² 这个数从哪来」，不是「电子为什么这样填」。
把它算作「原子物理」是过度解读。
另：该文件在 `lakefile.lean:65` 构建根中，但未进 `AxiomAuditEnhanced.lean` 的复核清单（0 命中），
因此其公理依赖**不在** `FOUNDATION_BASE.md` §1.3 的 335 条逐条审计范围内。

---

## 6. 证据索引（按文件）

| 文件 | 本文件引用的关键行 |
|---|---|
| `CSQIT_W1/Foundation.lean` | 48-62（`AxiomA` 七字段）、66-74（`AxiomC` 四字段）、1104（`planckMass`）、1265/1273/1281（三个 `:= True` 诠释） |
| `CSQIT_W1/CompilerAxioms.lean` | 128（`core_collapse`）、195（`core_collapse_independent_of_output`） |
| `CSQIT_W1/CoreCollapse.lean` | 57（`input_must_be_empty`） |
| `CSQIT_W1/IndependenceCheck.lean` | 209、233、249、259、269、441、484、726、790、1200、1349 |
| `CSQIT_W1/CurvatureEnergyRefutation.lean` | 75、88 |
| `CSQIT_W1/ObserverLayering.lean` | 50-53（层级标签）、59-111、197 |
| `CSQIT_W1/AlgebraicTimeCircle.lean` | 61（`curvature_energy`） |
| `CSQIT_V1Bridge/OrderAndFixedPoint.lean` | 73、87、160、169、195 |
| `CSQIT_V1Bridge/OrderMaximality.lean` | 63、77、100、144 |
| `CSQIT_V1Bridge/OrderUniqueness.lean` | 267 |
| `CSQIT_V1Bridge/OperadImpossibility.lean` | 172、193 |
| `CSQIT_V1Bridge/AmplitudeRigidity.lean` | 67、83、98、112、137、161 |
| `CSQIT_V1Bridge/CausalLayerSharpening.lean` | 260、273 |
| `CSQIT_V1Bridge/V23Interface.lean` | 111、121 |
| `CSQIT_LayerTower/Tower.lean` | 100-115、128、138、163、172、190、195 |
| `CSQIT_LayerTower/Top.lean` | 62、73 |
| `CSQIT_LayerTower/AxiomCMaximality.lean` | 119 |
| `CSQIT_LayerTower/Potential.lean` | 42、175、192、229 |
| `CSQIT_LayerCuts/Cuts.lean` | 144-205（`Module` 唯一用处）、223、235、264、287、295 |
| `CSQIT_Enhanced/Axioms.lean` | 265-284（`AxiomB`）、446-453（`AxiomD`）、554-557（`AxiomF`）、580-582（`AxiomG`）、607-610（`AxiomH`）、631-640（`AxiomI`）、687-690（`AxiomJ`）、728-745（三大解耦）、781-782、809、1014-1027（`AxiomK`）、1035 |
| `CSQIT_Enhanced/EnhancedModels.lean` | 426、435-436、438-441、670、746、1120、1132 |
| `CSQIT_Enhanced/PeriodicTable.lean` | 97-98、119 |

---

## 7. 怎么用这份文档、什么时候必须回来改它

**用法**：
- 引第一层结论时，写「在任何满足 `AxiomA`/`AxiomC` 的模型里……」，不写「在宇宙里……」。
- 引第一层结论时，它是**排除**；不要把它反过来当**描述**用。
- 第一层里凡涉及具体数值（420、105、289、8），一律写「在该 `def` 取值下为真」，不写「由公理推出」（依据 `FOUNDATION_BASE.md` §0.1 的措辞口径）。

**必须回来改它的三个触发条件**：
1. 新增任何 `Metric` / `Hilbert` / `Measure` / `TensorProduct` 结构 —— 第三层零命中表立即失效。
2. 修改 `amplitude_injective` 或给 `AxiomC` 增加加法/线性字段 —— §2.1 的七件缺口与第 8 条反向障碍需要重算。
3. 新增层间投影/粗粒化映射的定理 —— §4.2 与 §4.3 的「没有可陈述对象」结论需要撤回。

**不改变结论的操作**：新增 W1 数值定理、补 `#print axioms`、补文档措辞。
