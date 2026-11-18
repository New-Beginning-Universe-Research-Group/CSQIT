# ANALYSIS · 公理与假设层（第九轮，逐条）

> 工作区：`D:\CSQIT-v23-fix`。日期：2026-11-05。
> 方法：静态读取源码 + 机器抽取（[analysis_data.tsv](analysis_data.tsv)）+ 全量公理审计
> （[analysis_axioms.log](analysis_axioms.log)，474/474 条 `#print axioms`）。
> **本文件只读解析，未改动任何代码。** 发现的问题集中在 §4，待确认后单独处理。

## 0. 术语澄清（必须先说清）

1. **本库没有任何 Lean `axiom` 声明**。`#print axioms` 输出的公理只有
   `propext` / `Classical.choice` / `Quot.sound`（经典数学标准三公理），
   全库 `sorryAx = 0`（474/474 实测，见 [analysis_axioms.tsv](analysis_axioms.tsv)）。
2. 本文件讨论的"公理"是**类型类字段**（`class CompilerAxiom ... where`）与
   **定义选择**（`def` 里的字面值）。它们不是 Lean 内核公理，而是"假设某结构存在"
   的建模前提；其后果由 Lean 定理机器验证。
3. **四档判定**沿用前八轮：已证 / 依赖声明假设 / 未证且不可由现有公理推出 / 无法判定；
   量的档位（Forced / Free / External）沿用 [DETERMINACY.md](DETERMINACY.md)。

---

## 1. `CompilerAxiom` 五字段（逐字段）

定义位置：[CompilerAxioms.lean:60-97](CSQIT_W1/CompilerAxioms.lean#L60-L97)。

| # | 字段 | Lean 原句 | 类型 | 语义含义 |
|---|---|---|---|---|
| 1 | `compose` | `compose : C → C → C` | `C → C → C` | 两条规则可串联成一条新规则（"先 α 后 β"） |
| 2 | `assoc` | `assoc : ∀ α β γ : C, compose (compose α β) γ = compose α (compose β γ)` | `∀ α β γ : C, ... = ...` | 串联不依赖分组方式 |
| 3 | `input` | `input : C → List M` | `C → List M` | 每条规则记录其依赖的输入列表（"import 列表"） |
| 4 | `compose_input` | `compose_input : ∀ α β : C, input (compose α β) = input α ++ input β` | `∀ α β : C, ...` | 组合的依赖 = 两规则依赖的拼接 |
| 5 | `input_nodup` | `input_nodup : ∀ α : C, (input α).Nodup` | `∀ α : C, ...` | 依赖列表无重复 |

### 1.1 存在性实例（两实例，同载体 `(ℕ, ℕ)`）

[IndependenceCheck.lean:35-49](CSQIT_W1/IndependenceCheck.lean#L35-L49)：

| 实例 | compose | assoc | input | compose_input | input_nodup |
|---|---|---|---|---|---|
| `instNatAdd` | `a + b` | `Nat.add_assoc` | `fun _ => []` | `rfl` | `List.nodup_nil` |
| `instNatLeft` | `fun a _ => a` | `rfl` | `fun _ => []` | `rfl` | `List.nodup_nil` |

**两实例不等**：[instances_differ](CSQIT_W1/IndependenceCheck.lean#L53-L58)（在 (0,1) 处取值 1 vs 0，已证）。
含义：五字段**不唯一决定**任何结构值；这是 [no_determiner](CSQIT_W1/IndependenceCheck.lean#L190-L205) 系列独立性定理的锚点。

### 1.2 每个字段是否被定理真正使用

| 字段 | 使用的定理（源码位置） | 实际作用 |
|---|---|---|
| `compose` | `core_collapse`（[:127](CSQIT_W1/CompilerAxioms.lean#L127-L141)）、`compiler_theorem_summary`（[:211-215](CSQIT_W1/CompilerAxioms.lean#L211-L215)）、`instances_differ` | 用于构造 `α∘α` 自组合；是 Core Collapse 的必要构件 |
| `assoc` | **仅** `compiler_theorem_summary`（[:215](CSQIT_W1/CompilerAxioms.lean#L215)） | 对 Core Collapse **零贡献**；[MinimalCompilerAxiom](CSQIT_W1/AxiomIndependence.lean#L53-L57)（4 字段、无 assoc）重新证得同一结论 `minimal_core_collapse` |
| `input` | `core_collapse` 及全部推论 | 结论对象本身 |
| `compose_input` | `core_collapse`（[:129](CSQIT_W1/CompilerAxioms.lean#L129)） | 给出 `input (α∘α) = input α ++ input α` |
| `input_nodup` | `core_collapse`（[:128](CSQIT_W1/CompilerAxioms.lean#L128)） | 与上一条联合导致矛盾 |

**结论**：五字段中真正"干活"的是 `compose` + `compose_input` + `input_nodup`（3 条）；
`input` 是结论变量；`assoc` 是冗余字段（本库已形式化证明其冗余）。

### 1.3 它约束了什么 / 没约束什么

**约束了**（仅此而已）：
- `C` 上存在一个二元运算；
- 该运算结合（`assoc`）；
- 存在 `C → List M` 的映射 `input`；
- `input` 对 `compose` 精确可加（不是"次可加"）；
- 每个 `input α` 无重复。

**没有约束**：
- 任何数值常数（12/60/168、8/64/840、137+9/250、250/9、420、289、H₀…）：
  五字段的语句里不出现任何常数，也不引用 Foundation 的 def（已由
  `instances_differ` 与 `no_determiner` 形式化确认）；
- `M`、`C` 非空、势、可计算性、语义解释；
- `compose` 的交换性、幂等性、单位元（只要求结合）；
- 输出/观测行为（`output` 不在五字段内）。

### 1.4 一个必须写明的派生后果：`input` 恒为空

[core_collapse](CSQIT_W1/CompilerAxioms.lean#L127-L141) 已证：

```
[CA : CompilerAxiom M C] (α : C) : CA.input α = []
```

即**任何**满足五字段的模型里，所有规则的依赖列表都是空表。随之而来：

- `compose_input` 退化为 `[] = [] ++ []`；
- `input_nodup` 退化为 `[].Nodup`；
- "依赖追踪 / 增量编译 / 因果输入"的**非空**语义在五字段模型内**没有模型**
  （不是"未证"，而是"与公理矛盾"——恰好由本库自己的定理证明）。

因此：**凡以"规则带非空 import 列表"为前提的物理论述，在本框架内不可满足。**
若要建模真实编译器的依赖，必须修改公理（例如允许重复、或用次可加 `⊆` 代替精确等式）。
这是第九轮解析发现的最重要语义边界，登记于 §4-F1。

### 1.5 不要与 `AxiomA` 混淆

仓库里有两套公理类：

| 类 | 字段数 | 位置 | 使用者 |
|---|---|---|---|
| `CompilerAxiom` | 5 | [CompilerAxioms.lean:60](CSQIT_W1/CompilerAxioms.lean#L60) | `CompilerAxioms`、`AxiomIndependence`、`IndependenceCheck` 的模型定理 |
| `AxiomA`（旧/并行） | 7（多 `output`、`compose_output`） | [Foundation.lean:48-62](CSQIT_W1/Foundation.lean#L48-L62) | `CoreCollapse`、`TwoAspect`、`TwoAspectNoFinite`、`AxiomDerivation`、`CSQITWeaver` 等 |
| `AxiomC`（振幅） | 4 | [Foundation.lean:66-74](CSQIT_W1/Foundation.lean#L66-L74) | 相位/振幅相关模块 |

`CompilerAxioms.lean` 的文件注释声称旧 `AxiomA` 的 output 是"派生概念、不再需要"，
但**旧类并未被删除**，下游仍有 8 个文件引用 `AxiomA`。本轮只按要求解析五字段的
`CompilerAxiom`；`AxiomA` 的 7 字段不在本表范围内，但列入 §4-F10 的待清理项。

---

## 2. 诠释假设 1–7（逐条）

来源：[DETERMINACY.md §假设清单](DETERMINACY.md#L58-L82)、[LAWS.md 三级标注](LAWS.md)。
表中的"代码形态"指该假设在 Lean 源码里以什么形式出现。

| # | 假设原文（DETERMINACY） | 代码形态 | 是否可形式化 | 是否已形式化 |
|---|---|---|---|---|
| 1 | **素基底 P = {2,3,5,7}**（`Foundation.p1–p4` / `MinimalCost.mkBase`） | `def p1..p4 : ℕ`（[Foundation:130-133](CSQIT_W1/Foundation.lean#L130-L133)）；`def mkBase` | 可（作为显式参数或结构字段） | **否**：仅以字面 def 固定；其物理身份无定理。"必要性"已测（42 依赖 P），"唯一性"见 §4-F2 |
| 2 | **群阶 12/60/168**（`A4_order/A5_order/PSL27_order`） | `def A4_order : ℕ := 12` 等（[Foundation:108-110](CSQIT_W1/Foundation.lean#L108-L110)）；`A4_order_B` 等以 P 表达（[MinimalCost:151-157](CSQIT_W1/MinimalCost.lean#L151-L157)） | 可 | **部分**：`no_determiner` 定理证明"五字段不决定它们"（Free 档）；但"为什么是这三个群"无定理 |
| 3 | **lcm 闭包规则 "/2"**（`Foundation.totalClosure`） | `def totalClosure := lcm(lcm 12 60) 168 / 2`（[Foundation:114](CSQIT_W1/Foundation.lean#L114)） | 可 | **部分**：`totalClosure_eq_420` 证 lcm 计算；"/2 必要性"已测（"/3"→280≠420）；"/2 正确性"无定理 |
| 4 | **`closure_sequence_extended` 的字面模式**（8/64/420/840/…） | `def closure_sequence_extended`（[Foundation:565-574](CSQIT_W1/Foundation.lean#L565-L574)）前 8 项写死 | 可 | **部分**：`closure_sequence_extended_values` 展开前 8 项；8 的 `p₁³` 链接仅 `MinimalCost §4` 注释级；64 的指数 6 有 `level64_not_determined`（Free） |
| 5 | **CODATA 2018 / Planck 2018 经验数据** | **定理前提** `h_obs : observed_energy ... = 137.035999206`（[ObserverLayering:187-189](CSQIT_W1/ObserverLayering.lean#L187-L189)） | 可（作为参数） | **是（以假设形式）**：只作为前提出现，不进入任何定理结论；对应定理 `alpha_inv_absolute_error_bounded` 因前提≈结论而归 W |
| 6 | **基元选择原理"宇宙取最小素数解"** | 最小性本身是定理：`prime_solution_lex_min`、`mkBase_is_min_prime_solution`（[IndependenceCheck](CSQIT_W1/IndependenceCheck.lean)）；"宇宙如此选择"**无代码** | 可（作为选择公理/参数） | **部分**：最小性已证；**选择原理本身未形式化**（LAWS D5 标【含诠释假设】） |
| 7 | **层级映射假设"物理宇宙 ≃ ℕ 型层级分解结构"** | 模型内定理：`no_infinite_decomposition`、`prime_factorization_unique`、`tower_determined_by_individuals`、`hierarchy_picture`（[IndependenceCheck](CSQIT_W1/IndependenceCheck.lean)）；"物理宇宙"**无代码** | 可（作为同构/映射参数） | **部分**：形式模型内已证；映射本身未形式化（LAWS A5/E4 注明） |

**汇总**：7 条中，**0 条**已被形式化为"物理断言"；**3 条**（5、6、7）有对应的
形式化**数学内核**，但诠释部分仅存在于论文文字与 docstring；**4 条**（1–4）
只以字面 `def` 出现，其"应当取这些值"的主张没有定理支撑。

**A5 / D5 在 LAWS 中的位置**（用户特别点名）：

- **A5**（基底落在原子层上）：`IndependenceCheck.mkBase_slots_are_atoms` —— 模型内
  "四槽位全为素数"已证；"基底 = 宇宙基本构成"须调用假设 6。
- **D5**（基底 = 最小素数解）：`satisfiesQ_iff_weaving`、`mkBase_is_min_prime_solution`
  的数学部分已证；"宇宙取最小素数解"是假设 6。

---

## 3. 全部常量（逐条）

档位依据 [DETERMINACY.md 图谱](DETERMINACY.md#L30-L50)；"对应定理"均为已证且经审计。

| 常数 | 定义位置 | 定义体原文 | 档位 | 对应定理（源码） |
|---|---|---|---|---|
| **137 + 9/250** | [Foundation:143-144](CSQIT_W1/Foundation.lean#L143-L144) | `inverseAlpha := p1^p4 + p1^p2 + 1 + p2^2 / (p1 * p3^3)` | **Free**（编码值；物理对应 External） | `inverseAlpha_eq_137_036`（[165-166](CSQIT_W1/Foundation.lean#L165-L166)）；`MinimalCost.alpha_inv_mkBase_eq_137p036`；桥接 `alpha_inv_exact_eq_inverseFineStructure`（[WeaverPopulation:61-62](CSQIT_W1/WeaverPopulation.lean#L61-L62)，rfl） |
| **250/9** | [Foundation:148-149](CSQIT_W1/Foundation.lean#L148-L149) | `observerBridge := p1 * p3^3 / p2^2` | **Free** | `observerBridge_mkBase_eq_250_over_9`（[ObserverLayering:158-161](CSQIT_W1/ObserverLayering.lean#L158-L161)） |
| **420** | [Foundation:114](CSQIT_W1/Foundation.lean#L114) | `totalClosure := Nat.lcm (Nat.lcm A4_order A5_order) PSL27_order / 2` | **Forced**（给定 12/60/168 与 "/2"） | `totalClosure_eq_420`（[117-119](CSQIT_W1/Foundation.lean#L117-L119)）；`MinimalCost.closure_N_mkBase_eq_420`（[173-175](CSQIT_W1/MinimalCost.lean#L173-L175)） |
| **42** | 无 `def`（派生量） | `e1² − e3 = p1·p2·p4 = 2·3·7` | **Forced**（给定 P） | `e1_sq_sub_e3_eq_p1p2p4`（[QuantumCorrection:57-63](CSQIT_W1/QuantumCorrection.lean#L57-L63)）；依赖 `e1_mkBase_eq_17`、`e3_mkBase_eq_247`（[MinimalCost:121-131](CSQIT_W1/MinimalCost.lean#L121-L131)） |
| **105** | [ObserverLayering:59-60](CSQIT_W1/ObserverLayering.lean#L59-L60) | `alpha_level_n := mkBase.p2 * mkBase.p3 * mkBase.p4` | **Forced**（给定 P） | `alpha_level_n_eq_105`（[62-63](CSQIT_W1/ObserverLayering.lean#L62-L63)） |
| **8** | [Foundation:565-566](CSQIT_W1/Foundation.lean#L565-L566) | `closure_sequence_extended 0 => 8` | **Forced**（定理在 `MinimalCost` 的 p₁³ 模型内；字面链接仅注释级） | `IndependenceCheck.eight_unique_of_base`（[:361](CSQIT_W1/IndependenceCheck.lean#L361)）；`MinimalCost` 中 `p1^3=8` |
| **64** | [Foundation:567](CSQIT_W1/Foundation.lean#L567) | `closure_sequence_extended 1 => 64` | **Free**（指数 6 无规范来源） | `IndependenceCheck.level64_not_determined_by_fields`（[:311](CSQIT_W1/IndependenceCheck.lean#L311)） |
| **840** | [Foundation:569](CSQIT_W1/Foundation.lean#L569) | `closure_sequence_extended 3 => 840` | **Forced**（= lcm(12,60,168)） | `IndependenceCheck.eight_forty_unique_of_orders`（[:368](CSQIT_W1/IndependenceCheck.lean#L368)）；`closure_sequence_extended_values`（[577+](CSQIT_W1/Foundation.lean#L577)） |
| **12** | [Foundation:108](CSQIT_W1/Foundation.lean#L108) | `A4_order : ℕ := 12` | **Free** | `IndependenceCheck.order12_not_determined_by_fields`；`A4_order_B`（[MinimalCost:151](CSQIT_W1/MinimalCost.lean#L151)） |
| **60** | [Foundation:109](CSQIT_W1/Foundation.lean#L109) | `A5_order : ℕ := 60` | **Free** | `order60_not_determined_by_fields`；`A5_order_B`（[MinimalCost:154](CSQIT_W1/MinimalCost.lean#L154)） |
| **168** | [Foundation:110](CSQIT_W1/Foundation.lean#L110) | `PSL27_order : ℕ := 168` | **Free** | `order168_not_determined_by_fields`；`PSL27_order_B`（[MinimalCost:157](CSQIT_W1/MinimalCost.lean#L157)） |
| **289** | [Foundation:136-139](CSQIT_W1/Foundation.lean#L136-L139) | `S := p1+p2+p3+p4`；`darkEnergyNum := S ^ 2` | **Forced**（给定 P） | `S_eq_17`（[:190](CSQIT_W1/Foundation.lean#L190)）；`darkEnergyNum_eq_289`（[:197](CSQIT_W1/Foundation.lean#L197)） |
| **Ω_Λ = 289/420** | [PhysicalConnect:55](CSQIT_W1/PhysicalConnect.lean#L55) | `omega_Lambda : ℝ := 289 / (totalClosure : ℝ)` | **Forced**（编码值）；物理诠释 **External 且未形式化** | `omega_values_exact`（[63-69](CSQIT_W1/PhysicalConnect.lean#L63-L69)）；`omega_Lambda_eq_darkEnergyNum_ratio`（[74-78](CSQIT_W1/PhysicalConnect.lean#L74-L78)）；`cosmic_sum_eq_one`（[57-61](CSQIT_W1/PhysicalConnect.lean#L57-L61)） |
| **H₀** | [Foundation:161-162](CSQIT_W1/Foundation.lean#L161-L162) | `hubbleConstant := inverseFineStructure * (30 : ℝ) / 61` | **External**（以匹配经验 H₀≈67.4 为目标） | `hubbleConstant_eq`（[169-170](CSQIT_W1/Foundation.lean#L169-L170)，rfl）；`IndependenceCheck.hubble_not_determined_by_fields`（[:414](CSQIT_W1/IndependenceCheck.lean#L414)） |
| **30 / 61** | 同上（字面量） | `(30 : ℝ) / 61` | **Free**（定义选择；动机是经验 H₀） | 无独立定理；仅 `hubbleModel_30_eq_hubbleConstant`（`IndependenceCheck`，rfl）与 `hubble_not_determined` |

补充：`PhysicalConnect` 的 `omega_b := 20/420`、`omega_DM := 111/420` 也是字面分子
（[PhysicalConnect:47-48](CSQIT_W1/PhysicalConnect.lean#L47-L48)），不在用户清单内但同属
"定义选择 + 数值巧合"（`cosmic_sum_eq_one` 已证 20+111+289=420）。

---

## 4. 解析中发现的问题（与论文 / 宣称不符）

> 本节只登记，**未改任何代码/论文**。按用户要求，需确认后再动。

### F1（语义边界，最重要）：五字段强制 `input ≡ []`
`core_collapse` 是**无条件**定理（任意 `M C`、任意实例）。因此"依赖追踪"字段在
所有模型中都是空表；`compose_input` 的"精确可加"只在空表上成立。
**后果**：任何"规则携带非空 import 列表"的建模（含论文中"编译器依赖"的类比）
在本框架内**不可满足**。若要保留该类比，公理必须改弱（如次可加 `⊆`），
但那样 Core Collapse 不再成立——两者互斥。
（论文把这条读作"宇宙底层规则自包含"，逻辑上成立；但不能同时声称"追踪依赖"。）

### F2（R 级）："唯一素基底"是空条件
[SequenceStructure.lean:429-441](CSQIT_W1/SequenceStructure.lean#L429-L441)：
`base_uniqueness_by_exclusion` 与 `unique_base_is_2357` 的陈述是
`MUST_HAVE ⊆ B → B ⊆ MUST_HAVE → B = MUST_HAVE`，
证明仅 `Finset.Subset.antisymm`（集合外延性），**不证明任何基底唯一性**。
论文 [paper_revision/csqit_w1_paper.tex:486-492](paper_revision/csqit_w1_paper.tex#L486-L492)
以 "Unique Basis" 为标题、并在 [:524-526](paper_revision/csqit_w1_paper.tex#L524-L526)
称唯一性由它证明——**陈述强度与论文宣称不符**。
（论文正文其实把空条件写出来了，但标题与摘要的 "unique prime basis" 会误导。）

### F3（R 级，共 7 条）：前提即结论的空条件定理
见 [ANALYSIS_theorems.md §5](ANALYSIS_theorems.md)。典型：
`weaver_mass_scale_conditional (h_64 : P) : P`、
`strong_cp_naturalness_theorem (h_numeric : P) : P`、
`axion_mass_topological_solution (h_field_eq : P) : P`。
数学上恒真，但零信息；名字与所在小节宣称物理结论。

### F4：Ω_Λ 的记法更正（沿用第二轮）
`omega_Lambda` 定义一直是 `289 / (totalClosure : ℝ)`（分数），
不是裸 `289`。15/16 号审计的简写已失真，本轮复核确认定义未变——
[PhysicalConnect:50-55](CSQIT_W1/PhysicalConnect.lean#L50-L55) 的 docstring 已写明。

### F5：8 / 64 / 840 的来源分层
`closure_sequence_extended` 前 8 项全部写死（[Foundation:565-574](CSQIT_W1/Foundation.lean#L565-L574)）。
其中只有 420 有独立定义链（lcm/2）；8 的 `p₁³` 来源仅在 `MinimalCost §4` 注释里，
**未形式化**；64 的指数 6 无来源（Free，且有定理）；840 = lcm(12,60,168) 可算但未单列定理。

### F6：30/61 无来源
`hubbleConstant` 里的 `30`、`61` 是字面量，全库无定理推导其来源。
DETERMINACY 将其列为 Free（动机为经验 H₀），本轮确认：**它不属于基底 P 的函数**。

### F7：CODATA 只以定理前提出现
唯一塞入点是 `h_obs`（[ObserverLayering:187-189](CSQIT_W1/ObserverLayering.lean#L187-L189)）。
对应定理 `alpha_inv_absolute_error_bounded` 的结论只是"若观测值等于精确值，则误差<1e-5"，
属 W 级（措辞易误读），不是 R。

### F8：`satisfiesQ_iff_nat_add` 的右侧非规范形
[IndependenceCheck](CSQIT_W1/IndependenceCheck.lean) 的该定理右侧写成
`a*b*c + a*b*d + a*c*d + b*c*d + a*b*d`（`abd` 出现两次），
等价于 `abc + 2abd + acd + bcd`。**陈述正确**，但不是通常的对称多项式规范形；
属于 W 级措辞问题，不影响证明。

### F9：论文统计已过时
- 论文称 28 个模块 / 9,825 行 / **451** 条 theorem-lemma（[:533-535](paper_revision/csqit_w1_paper.tex#L533-L535)）；
  本轮实测 **29 个源码模块 / 474 条 theorem-lemma**。
- 论文称 GB 编译不过且**恰好一个 sorry**（[:598-607](paper_revision/csqit_w1_paper.tex#L598-L607)、
  [:616-619](paper_revision/csqit_w1_paper.tex#L616-L619)）；
  第八轮已墓碑化 GB，**构建内零 sorry**。论文需更新。
- 论文称 "unique prime basis"（[:48](paper_revision/csqit_w1_paper.tex#L48)）——见 F2。

### F10（待清理，非本轮任务）
`AxiomA`（7 字段）与 `CompilerAxiom`（5 字段）并存，8 个下游文件仍用旧类；
`CompilerAxioms.lean` 的注释宣称 output 已"不再需要"，但旧结构仍在构建内。
不是错误，是技术债。

---

## 5. 复现方式

```bash
cd /mnt/d/CSQIT-v23-fix
python3 tools/extract_theorems.py --audit          # 生成 analysis_data.tsv + AxiomAuditAll.lean
lake env lean CSQIT_W1/AxiomAuditAll.lean > analysis_axioms.log 2>&1
python3 tools/extract_theorems.py --axioms analysis_axioms.log   # 生成 analysis_axioms.tsv
python3 tools/build_analysis.py                    # 生成 ANALYSIS_theorems.md
```

实测：审计文件 0 error、0 `sorryAx`，474/474 条均输出公理集。

---

## 6. PeriodicTable.lean 审计纳入（第二十九轮，2026-11-13）

### 6.1 文件与构建地位
- 文件：[CSQIT_Enhanced/PeriodicTable.lean](CSQIT_Enhanced/PeriodicTable.lean)，456 行。
- 构建根：[lakefile.lean:65](lakefile.lean#L65)（`CSQIT_Enhanced` roots 第 3 项）⇒ 默认目标 `lake build` **确实依赖它**。
- git 状态：**未跟踪**（`git status --porcelain` 输出 `?? CSQIT_Enhanced/PeriodicTable.lean`）；**未被忽略**（`git check-ignore` 无命中）。本轮**未执行 `git add`、未提交**。

### 6.2 公理 / opaque / sorry 扫描
- `grep -nE '^\s*(axiom|opaque)\b|sorry|admit'` 于该文件**零命中**：无 Lean `axiom`、无 `opaque`、无 `sorry`/`admit`。
- 文件内只有 `def` / `theorem` / `structure` / `inductive` / `instance` / `noncomputable def`。

### 6.3 三条 theorem 的 `#print axioms`（实测）
| 定理 | 位置 | 公理集 | tier |
|---|---|---|---|
| `shell_capacity_from_quantum_states` | [:119-139](CSQIT_Enhanced/PeriodicTable.lean#L119-L139) | `propext, Classical.choice, Quot.sound` | W1 |
| `ideal_period_length` | [:234-243](CSQIT_Enhanced/PeriodicTable.lean#L234-L243) | `propext, Classical.choice, Quot.sound` | W3（空弱存在） |
| `noble_gas_is_balanced_state` | [:279-280](CSQIT_Enhanced/PeriodicTable.lean#L279-L280) | `propext, Classical.choice, Quot.sound` | W3（定义重言） |

全部仅标准三公理，`sorryAx = 0`。

### 6.4 与既有 21 公理类的关系（审计重点）
- 该文件 `import CSQIT_Enhanced.Axioms`（[:49](CSQIT_Enhanced/PeriodicTable.lean#L49)），但**三条定理的陈述与证明均不引用任何公理类**（`AxiomA`、`AxiomA'`、`AxiomB'`、`AxiomC`、`AxiomC'`、`AxiomJ'`、`AxiomD'` 全部未出现）。
- 其依赖的外部声明仅为 Mathlib：`Finset.sum`、`Nat.pow`、`Real.pi`（[:309](CSQIT_Enhanced/PeriodicTable.lean#L309)）、`Real.exp`（[:358](CSQIT_Enhanced/PeriodicTable.lean#L358)）、实幂 `^`（[:346-359](CSQIT_Enhanced/PeriodicTable.lean#L346-L359)），以及战术 `norm_num`/`ring`/`omega`/`linarith`。
- **结论：不存在"既有 21 公理类之外的新公理依赖"**——因为文件根本没有任何公理类依赖。这属于**审计口径漏项**（此前未登记），不是新的公理来源。

### 6.5 三条定理的内容强度（防止误当物理结论）
1. `shell_capacity_from_quantum_states`：证 `2n² = 2·∑_{l<n}(2l+1)`，即"前 n 个奇数之和 = n²"的算术恒等式（`shell_capacity`=[:84](CSQIT_Enhanced/PeriodicTable.lean#L84)、`angular_momentum_states`=[:107](CSQIT_Enhanced/PeriodicTable.lean#L107)）。**真但初等**。
2. `ideal_period_length`：形如 `∃ p ∈ ideal_periods, (p.period_number = n → p.length = shell_capacity n)`。`ideal_periods` 非空（[:217-225](CSQIT_Enhanced/PeriodicTable.lean#L217-L225)，7 项），取一个 `period_number ≠ n` 的元素即令蕴含式空真成立；**不主张**真实周期长度等于壳层容量（实际为 2,8,8,18,18,32,32，文件自述见 [:230](CSQIT_Enhanced/PeriodicTable.lean#L230)）。属空弱存在。
3. `noble_gas_is_balanced_state`：`is_noble_gas atom → is_neutral atom ∧ is_closed_shell atom`，而 `is_noble_gas := is_neutral ∧ is_closed_shell`（[:187-188](CSQIT_Enhanced/PeriodicTable.lean#L187-L188)），证明为 `:= h`。**前提即结论**（F3 型定义重言）。

### 6.6 头部无定理支撑的定量声明（属"无支撑"，非公理问题）
头部注释声称 `R²=0.957`、平均相对误差 `1.8%`、纠缠熵-半径相关系数 `0.91`、惰性气体误差 `0.013Å`、超重元素 `1.8%`（[:34-38](CSQIT_Enhanced/PeriodicTable.lean#L34-L38)，另见 [:294-296](CSQIT_Enhanced/PeriodicTable.lean#L294-L296)）。**这些数值不出现在任何 theorem 的陈述或证明中**，无形式化支撑，对外应列为无支撑经验值（与 C6 同类）。
