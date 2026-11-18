# FOUNDATION_BASE · 可依赖基座（CSQIT-v23-fix 定稿）

> 生成日期：2026-11-10。工作区：`D:\CSQIT-v23-fix`。
> 本轮只读源码与既有构建产物：**未改任何 `.lean`**、**未新增 `axiom` / `sorry`**、
> **未改动既有 474 条声明的陈述与证明**。唯一新增的是本文档与 `foundation_base.tsv`。
> 逐条机器可读清单见 [foundation_base.tsv](file:///D:/CSQIT-v23-fix/foundation_base.tsv)。

---

## 0. 这份东西怎么用 / 什么情况下必须回来改它

### 0.1 怎么用

引用一条结论前，先在 `foundation_base.tsv` 查它属于哪一档：

| 档位 | 含义 | 引用规则 |
|---|---|---|
| `W1` + `unconditional=yes` | 闭式定理，无自由参数 | **可直接引用**。引用时带上 `文件:行号` + 定理全名。 |
| `W2` | 条件定理，有显式前提 | **必须连前提一起原样引用**；不得只写定理名。去掉前提即失效。 |
| `W3` | 依赖定义选择或物理诠释 | 只能作为「在……诠释下」的陈述引用，**不得当作数学结论**。 |
| `DENIED` | 已证否 / 禁止当前提 | **不得以任何形式作为前提或论据**。见 §6。 |
| `CANDIDATE` | 候选模块的接口/骨架 | 只能引用其**已机检的那部分**；不得把接口当结论。见 §7。 |

两个字段不要混：

- **`tier`** 回答「这条结论的强度」；
- **`basis`** 回答「这条结论依赖什么」，取值只有三类：
  - `axioms`：确实从 `CompilerAxiom` / `AxiomA` / `AxiomC` 的结构字段走出；
  - `def:<名字>`：数值由字面 `def` 锁定（如 `def:mkBase`、`def:totalClosure`）；
  - `external:<来源>`：数值来自框架外（如 `external:CODATA`、`external:H0`）。

`unconditional` 只回答「陈述里有没有自由参数」，与 `basis` 无关。
所以会出现 `unconditional=yes` + `basis=def:mkBase` 的行——这是正常的：
该命题无条件为真，但它的**数值内容**来自字面定义，不来自公理。

### 0.2 措辞禁令（硬规则）

1. 凡 `basis` 为 `def:*` 或 `external:*` 的数值，**不得**写成「由公理推出」。
   正确写法：「在 `def:mkBase` 取 `(2,3,5,7)` 的前提下为真」。
2. `no_determiner` 一族的结论方向相反：它们证明「五字段不决定该数值」。
   这两件事必须能对读而不打架：
   - 「`42` 在 `mkBase` 下为真」= 给定字面基底后的算术事实；
   - 「五字段不决定 `42`」= 换基底则值变，公理照常成立。
   两句同时成立，不矛盾；任何一句被单独放大成「CSQIT 推出 42」都是越界。
3. 档位口径统一用仓库原生的 **W1 / W2 / W3**（判定细则见 `TIER_CRITERIA.md`）。
   其他文档里的 A/B/C/D 与本档的映射：
   `A ≈ W1 + unconditional=yes`；`B / 条件 ≈ W2`；`C ≈ W3`；`D ≈ DENIED`。
   `CSQIT_LayerTower/DESIGN.md` 与 `CSQIT_LayerCuts/Cuts.lean` 用的是 A/B/C/D 写法，
   引用它们时按此表换算，**不要**把它们的「A 档」直接当作本表的 W1。

### 0.3 什么情况下必须回来改这份文档

出现下列任一情况，本文档立即失效，必须先改再引用：

1. `.lean` 里的定理**新增、删除或改陈述**（改了 `文件:行号` 或名字）；
2. `lean-toolchain` 或 `lake-manifest.json` 的 mathlib pin 变动；
3. `CompilerAxiom` / `AxiomA` / `AxiomC` / `AxiomA'` / `AxiomC'` 的**字段增删**；
4. 全库出现任何真实 `axiom` 声明或 `sorryAx`（当前为 0，见 §1）；
5. 某个 `CANDIDATE` 模块被提升为基座，或某条 `DENIED` 被重新证明（几乎不可能，但要查）；
6. `TIER_CRITERIA.md` 的档位判据被修改。

---

## 1. 环境与内核层

### 1.1 工具链与 pin（照此可复现）

| 项 | 值 | 位置 |
|---|---|---|
| Lean 工具链 | `leanprover/lean4:v4.29.0-rc6` | `lean-toolchain` |
| Mathlib pin | `6fc4d4f887b81826d7e577d31ff43075f0833dc9` | `lakefile.lean:7-8`、`lake-manifest.json` |
| 包名 / 版本 | `CSQIT_W1` / `13.1.0` | `lakefile.lean:4-5` |
| 构建根 | 5 个 `lean_lib`：`CSQIT_W1`(32 roots)、`CSQIT_Enhanced`(5)、`CSQIT_V1Bridge`(24)、`CSQIT_LayerTower`(4)、`CSQIT_LayerCuts`(1) | [lakefile.lean:22-119](file:///D:/CSQIT-v23-fix/lakefile.lean#L22) |

**环境坑（必须知道）**：Windows 侧 elan 只有 `v4.29.1`，与 toolchain 不符；
实际构建必须在 WSL 内进行，`/usr/bin/lean` 为 4.29.0-rc6，仓库挂载在 `/mnt/d/CSQIT-v23-fix`。

复现命令（单进程，勿并发）：

```bash
wsl -- bash -lc 'cd /mnt/d/CSQIT-v23-fix && export GIT_CEILING_DIRECTORIES=/mnt/d && lake build'
```

最近一次全量构建：**2389 jobs，退出码 0，全绿**（含 LayerTower / LayerCuts）。

### 1.2 实际依赖的公理

- **全库无 Lean `axiom` 声明**（`^axiom ` 零命中）。假设全部以 `class` 字段或定理参数形式出现。
- `#print axioms` 只出现标准三公理：`propext`、`Classical.choice`、`Quot.sound`。
- 部分结构/算术定理更弱：仅 `propext`（如整个 `core_collapse` 族、Enhanced 的 Bridge 族），
  或 `none`（如 `Foundation.totalClosure_eq_420`、`no_determiner`）。
- `sorryAx = 0`。仓库内文本 "sorry" 命中全部位于注释；唯一的真 `sorry` 在退役文件
  `GenerationBridge_legacy.lean.disabled`（旧 :1427），**不在构建内**。
- 逐条实测覆盖（见 §1.3）：四个候选模块（`CSQIT_V1Bridge` / `CSQIT_LayerTower` /
  `CSQIT_LayerCuts` / `CSQIT_Enhanced`）共 335 条声明，可具名 325 条**全部**逐条跑过
  `#print axioms`：228 `std3` / 48 `propext+quot` / 19 `propext` / 30 `none`；
  10 条 `private` 或注释伪声明不可具名（逐条原因见 §1.3）。`sorryAx = 0`，非标准公理 0。
- 审计产物：`analysis_axioms.tsv`（474 行逐条 `full_name → axioms`）、`analysis_axioms.log`、
  `CSQIT_W1/AxiomAudit.lean`（42 条核心定理，纯审计文件，不在 roots）。

**结论**：内核层可完全信任，没有隐藏的非标准公理。任何「某结论依赖了未声明公理」的
质疑，都可以用 `#print axioms <全名>` 当场复核。

逐定理公理集见 `analysis_axioms.tsv`（474 行）；四个候选模块的逐条实测见 §1.3。

### 1.3 逐条实测覆盖（2026-11-10）

对 `CSQIT_V1Bridge` / `CSQIT_LayerTower` / `CSQIT_LayerCuts` / `CSQIT_Enhanced` 的**全部
theorem/lemma** 逐条执行 `#print axioms`。审计文件放在仓库外（`D:\csqit-audit`），
不入库、不改构建面、不新增审计模块。

| 目录 | 声明总数 | 可具名 | 已审计 | std3 | propext+quot | propext | none |
|---|---|---|---|---|---|---|---|
| `CSQIT_LayerCuts` | 16 | 16 | 16 | 16 | 0 | 0 | 0 |
| `CSQIT_LayerTower` | 40 | 40 | 40 | 39 | 0 | 0 | 1 |
| `CSQIT_Enhanced` | 39 | 37 | 37 | 25 | 2 | 6 | 4 |
| `CSQIT_V1Bridge` | 240 | 232 | 232 | 148 | 46 | 13 | 25 |
| **合计** | **335** | **325** | **325** | **228** | **48** | **19** | **30** |

遗漏 10 条，原因逐条：

- `CSQIT_Enhanced` 2 条 `private lemma`：`val_add_eq`（EnhancedModels.lean:218）、
  `normSq_pow`（:674），无法按名引用；
- `CSQIT_V1Bridge` 4 条 `private`：`pow_eq_absorbs_le`、`circle_exp_pow`、`axiomC_ext`、
  `pow_eq_absorbs_le_zero`；
- `CSQIT_V1Bridge` 4 条注释中的伪声明（`h1`、`h2`、`_toCircle_inj_placeholder`、`bridge`），
  不是真实声明。

private 引理的公理集由使用它们的公开定理传递覆盖；若需逐条，只能改源码去 `private`（本轮不改）。

另补跑 4 条非定理声明（`AdditivePotential`、`witnessPotential`、`pathLapForm`、`compressionRatio`），
均为 `std3`。

**零异常**：335 条候选中无一条出现 `sorryAx`，无一条出现标准三公理之外的公理。

#### 与旧文档不一致的 10 处（原文 → 实测 → 原因）

> 下表「原写」列中的 `std3*` 是**历史记录**，说明该行此前只做过模块级审计；
> 它已不是任何现存字段的合法取值（见 §9）。当前 `foundation_base.tsv` 与本文其余各表中
> 的 `axioms` 值均为上表（§1.3 覆盖表）口径的实测结果。

| 声明 | 原写 | 实测 | 原因 |
|---|---|---|---|
| `fin7_opweaving_nonvacuous` | `propext` | `std3` | **实质错标**：该定理经 `Complex.normSq` 与 `Fin` 实例间接用到 `Classical.choice`；原值是照相邻 collapse 定理类推，未实测 |
| `no_uniform_compatible_order` | `std3*` | `propext` | `std3*` 是模块级上界，实测只用 `propext` |
| `no_uniform_fixed_point_five` | `std3*` | `propext+quot` | 上界收紧 |
| `no_upper_bound_of_opposite_edges` | `std3*` | `none` | 纯 Prop 论证，无公理 |
| `no_maximal_compatible_order` | `std3*` | `none` | 同上 |
| `not_universally_total` | `std3*` | `propext+quot` | 上界收紧 |
| `composePow_add` | `std3*` | `propext+quot` | 上界收紧 |
| `witnessHom_classification` | `std3*` | `propext` | 上界收紧 |
| `conditional_order` | `std3*` | `none` | 纯 Prop 论证，无公理 |
| `pair_two_compatible_orders_opposite` | `std3*` | `std3` | 原上界已是最小集合 |

其余 24 处 `std3*` 实测即 `std3`，属上界收敛，不构成错标。

---

## 2. 公理与定义层

### 2.1 `CompilerAxiom`（五字段）

定义：[CompilerAxioms.lean:60](file:///D:/CSQIT-v23-fix/CSQIT_W1/CompilerAxioms.lean#L60)。

| 字段 | 行 | 约束什么 |
|---|---|---|
| `compose : C → C → C` | :66 | 规则可组合 |
| `assoc` | :74 | 组合满足结合律 |
| `input : C → List M` | :81 | 每条规则携带一个依赖列表 |
| `compose_input : input(α∘β) = input α ++ input β` | :89 | 依赖按拼接传递 |
| `input_nodup : (input α).Nodup` | :97 | 同一依赖不重复 |

**真正约束了什么**：`compose_input` + `input_nodup` 与「非空 `input`」逻辑不相容，
于是 `input α = []` 对所有 `α` 无条件成立（`core_collapse`，:128）。

**不约束什么**：它**没有任何数值字段**。`C`、`M` 是任意类型，五个字段里不出现
任何自然数、实数或常数。因此：

> **五字段不决定任何数值。** 这是 `no_determiner` 一族（[IndependenceCheck.lean:209](file:///D:/CSQIT-v23-fix/CSQIT_W1/IndependenceCheck.lean#L209)）
> 的内容：对任意「五字段相同、数值不同」的模型族，都不存在从五字段到该数值的函数。
> **任何「从公理推出某常数」的说法，都不能引用这套代码来支撑。**

### 2.2 `AxiomA`（七字段）

定义：[Foundation.lean:48](file:///D:/CSQIT-v23-fix/CSQIT_W1/Foundation.lean#L48)。
字段：`input`(:50)、`output`(:52)、`input_nodup`(:54)、`compose`(:56)、
`compose_input`(:58)、`compose_output`(:60)、`compose_assoc`(:62)。

- **约束**：`input` 同样恒空（`base_input_empty`）；`output` 满足右零性
  `output(α∘β) = output β`。
- **不约束**：`M`、`C` 的具体内容；`output` 的取值；任何常数。
  `output` 在可交换 `compose` 下退化为常函数（`two_aspect_dichotomy_no_finite`）。

### 2.3 `AxiomC`（四字段）

定义：[Foundation.lean:66](file:///D:/CSQIT-v23-fix/CSQIT_W1/Foundation.lean#L66)。
字段：`amplitude : C → ℂ`(:68)、`norm_one : ‖amp α‖² = 1`(:70)、
`comp_rule : amp(α∘β) = amp α · amp β`(:72)、`amplitude_injective`(:74)。

- **约束**：振幅取值在单位圆上、乘性、单射。三者合起来非常强：
  `compose` 被振幅完全决定（`compose_forced_by_amplitude`，[AmplitudeRigidity.lean:83](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/AmplitudeRigidity.lean#L83)）。
- **不约束**：`amplitude` 的具体函数；任何物理常数。`no_determiner` 同样适用于振幅层
  （`GaugeAndEndo.lean` 的 `altAxiomC`：同一 `compose` 上可有两个合法 `AxiomC`）。

### 2.4 增强版 `AxiomA'` / `AxiomC'`

定义：[CSQIT_Enhanced/Axioms.lean:199](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/Axioms.lean#L199) 与 `:828`。
`AxiomA'` 保留 `compose_input` + `input_nodup`，故同样强制 `input ≡ []`
（`enhanced_input_empty`）。`AxiomA'` 新增的 `compose_output'` 不改变这一结论。

### 2.5 一个必须记住的推论

`core_collapse` 不是「宇宙没有输入」的物理定理，而是「这组字段自相矛盾地排除了非空输入」。
它在 A 档，可无条件引用；但引用时必须写成**模型内**结论：
「任何满足 `CompilerAxiom` 五字段的模型，其 `input` 恒为空」。

---

## 3. A 档（W1 + 无条件，可直接引用）

> 判据：闭式陈述、无自由参数、无经验输入、无未证假设。
> `basis` 见括号；`def:*` 表示数值由字面 `def` 锁定，按 §0.2 措辞禁令引用。

### 3.1 结构 / 坍缩族（`basis=axioms`）

| 定理 | 位置 | 公理集 | 说明 |
|---|---|---|---|
| `core_collapse` | [CompilerAxioms.lean:128](file:///D:/CSQIT-v23-fix/CSQIT_W1/CompilerAxioms.lean#L128) | `propext` | `CA.input α = []` |
| `core_collapse_length_zero` | :146 | `propext` | 依赖长度为 0 |
| `no_dependency` | :154 | `propext` | `x ∉ input α` |
| `core_collapse_independent_of_output` | :195 | `propext` | 与 `output` 无关 |
| `core_collapse_summary` | [CoreCollapse.lean:150](file:///D:/CSQIT-v23-fix/CSQIT_W1/CoreCollapse.lean#L150) | `propext` | 汇总形式 |
| `no_causal_input` | [CoreCollapse.lean:83](file:///D:/CSQIT-v23-fix/CSQIT_W1/CoreCollapse.lean#L83) | `propext` | 同上 |
| `minimal_core_collapse` | [AxiomIndependence.lean:66](file:///D:/CSQIT-v23-fix/CSQIT_W1/AxiomIndependence.lean#L66) | `propext` | 去掉 `assoc` 仍成立 |
| `base_input_empty` | [Bridge.lean:37](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/Bridge.lean#L37) | `propext` | `AxiomA` 版 |
| `base_weaving_vacuous` | :59 | `propext` | `weaving_axiom` 前提恒假 |
| `enhanced_input_empty` | :72 | `propext` | `AxiomA'` 版 |
| `enhanced_weaving_vacuous` | :97 | `propext` | `weaving_axiom'` 前提恒假 |
| `two_aspect_dichotomy_no_finite` | [TwoAspectNoFinite.lean:54](file:///D:/CSQIT-v23-fix/CSQIT_W1/TwoAspectNoFinite.lean#L54) | `std3` | `output` 常值 ∨ 振幅非单射 |

### 3.2 数值族（`basis=def:*`，无条件但数值由字面定义锁定）

| 定理 | 位置 | 公理集 | basis | 语义 |
|---|---|---|---|---|
| `e1_sq_sub_e3_eq_p1p2p4` | [QuantumCorrection.lean:58](file:///D:/CSQIT-v23-fix/CSQIT_W1/QuantumCorrection.lean#L58) | `std3` | `def:mkBase` | 在 `mkBase=(2,3,5,7)` 下 `e₁²−e₃ = 42` |
| `e3_from_e1_sq` | :67 | `std3` | `def:mkBase` | 上式改写 |
| `alpha_level_n_eq_105` | [ObserverLayering.lean:63](file:///D:/CSQIT-v23-fix/CSQIT_W1/ObserverLayering.lean#L63) | `std3` | `def:mkBase` | `n_α = 105` |
| `alpha_level_angle` | :80 | `std3` | `def:totalClosure` | 角度 `= π/2` |
| `cos_at_alpha_level` | :99 | `std3` | `def:totalClosure` | `cos = 0` |
| `sin_at_alpha_level` | :108 | `std3` | `def:totalClosure` | `sin = 1` |
| `totalClosure_eq_420` | [Foundation.lean:117](file:///D:/CSQIT-v23-fix/CSQIT_W1/Foundation.lean#L117) | `none` | `def:totalClosure` | `lcm(12,60,168)/2 = 420` |
| `darkEnergyNum_eq_289` | [Foundation.lean:197](file:///D:/CSQIT-v23-fix/CSQIT_W1/Foundation.lean#L197) | `propext` | `def:darkEnergyNum` | `S² = 289` |
| `inverseAlpha_eq_137_036` | [Foundation.lean:165](file:///D:/CSQIT-v23-fix/CSQIT_W1/Foundation.lean#L165) | `std3` | `def:inverseAlpha` | `= 137 + 9/250` |
| `hubbleConstant_eq` | [Foundation.lean:169](file:///D:/CSQIT-v23-fix/CSQIT_W1/Foundation.lean#L169) | `std3` | `external:H0` | `= α⁻¹·30/61`（`30/61` 为外部字面） |
| `alpha_inv_exact_eq_inverseFineStructure` | [WeaverPopulation.lean:65](file:///D:/CSQIT-v23-fix/CSQIT_W1/WeaverPopulation.lean#L65) | `std3` | `def:inverseAlpha` | 两种编码相等（`rfl`） |
| `declaration_alpha_inv_consistency` | [Declaration.lean:119](file:///D:/CSQIT-v23-fix/CSQIT_W1/Declaration.lean#L119) | `std3` | `def:inverseAlpha` | 同上，集中声明版 |
| `omega_Lambda_eq_darkEnergyNum_ratio` | [PhysicalConnect.lean:79](file:///D:/CSQIT-v23-fix/CSQIT_W1/PhysicalConnect.lean#L79) | `std3` | `def:darkEnergyNum` | 编码值 `= 289/420` |
| `union_of_prime_factors_eq_base` | [SequenceStructure.lean:313](file:///D:/CSQIT-v23-fix/CSQIT_W1/SequenceStructure.lean#L313) | `std3` | `def:group_prime_factors` | 三群素因子并 `= {2,3,5,7}` |
| `MUST_HAVE_eq_base` | [SequenceStructure.lean:392](file:///D:/CSQIT-v23-fix/CSQIT_W1/SequenceStructure.lean#L392) | `std3` | `def:group_prime_factors` | 同上 |
| `no_infinite_decomposition` | [IndependenceCheck.lean:1349](file:///D:/CSQIT-v23-fix/CSQIT_W1/IndependenceCheck.lean#L1349) | `propext+quot` | `axioms` | ℕ 上无无穷真因子链 |

### 3.3 no-go 族（A 档，否定式，可直接当前提）

| 定理 | 位置 | 内容 |
|---|---|---|
| `curvature_energy_not_strict_decreasing` | [CurvatureEnergyRefutation.lean:75](file:///D:/CSQIT-v23-fix/CSQIT_W1/CurvatureEnergyRefutation.lean#L75) | 全定义域严格递减为假 |
| `curvature_energy_counterexample` | :88 | 显式反例（`1 < 8` 但 `ce 1 < ce 8`） |
| `no_uniform_compatible_order` | [OrderAndFixedPoint.lean:73](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/OrderAndFixedPoint.lean#L73) | 五字段不能统一决定相容严格序 |
| `no_uniform_fixed_point_five` | :195 | 五字段不保证 `α∘α = α` 有解 |
| `no_surjective_self_pi` | [OperadImpossibility.lean:172](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/OperadImpossibility.lean#L172) | 非平凡 `α` 上无满射 `α → (α→α)` |
| `no_surjective_self_map_of_axiomA` | :193 | `AxiomA` 载体上的同名否定 |
| `no_upper_bound_of_opposite_edges` | [OrderMaximality.lean:63](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/OrderMaximality.lean#L63) | 反向边排除一切共同上界 |
| `no_maximal_compatible_order` | :77 | 无反自反传递关系同时包含两条反向序 |
| `pair_two_compatible_orders_opposite` | :100 | 乘积模型上的具体反例 |
| `not_universally_total` | :144 | 全序性不可由纯 `AxiomA` 普遍导出 |

### 3.4 刚性 / 桥接族（A 档）

| 定理 | 位置 | 内容 |
|---|---|---|
| `compose_forced_by_amplitude` | [AmplitudeRigidity.lean:83](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/AmplitudeRigidity.lean#L83) | 同振幅 ⇒ 同 `compose` |
| `compose_eq_left_iff_amplitude_eq_one` | :137 | `x∘y = x ⟺ amp y = 1` |
| `exists_compatible_order_iff_amplitude_ne_one` | :161 | 存在相容序 ⟺ `1 ∉ range(amp)` |
| `compatible_order_exists_iff_of_same_amplitude` | :180 | 同振幅 ⇒ 序存在性相同 |
| `add_amplitude_without_causality` | :217 | 可加振幅模型无因果层 |
| `leftAbsorbing_no_amplitude_no_layer` | :232 | 左吸收模型无振幅、无层 |
| `causal_order_unique_iff_reach_total` | [OrderUniqueness.lean:267](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/OrderUniqueness.lean#L267) | 序唯一 ⟺ 可达全序 |
| `witnessHom_classification` | [FreeModel.lean:109](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/FreeModel.lean#L109) | 见证模型同态全分类 |
| `witnessHom_amplitude` | :179 | 同态振幅 `= amp(φ0)^(n+1)` |
| `composePow_add` | :84 | 幂组合可加 |
| `fin_no_causal_layer` | [V23Interface.lean:111](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/V23Interface.lean#L111) | `Fin n` 模型无因果层 |
| `v23Finite_amplitude_without_causality` | :121 | 有限模型振幅与因果性无关 |

### 3.5 LayerTower 中的 A 档（可引用，但归属候选模块）

`layer_input_empty`（[Tower.lean:190](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Tower.lean#L190)）、
`top_input_empty`(:195)、`top_is_colimit`(:138)、`top_model_exists`(:128)、
`witnessTower_top_no_fixed_point`([Top.lean:62](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Top.lean#L62)）、
`witnessTower_top_no_self_generation`(:73)、
`pairTower_top_no_maximal_order`([AxiomCMaximality.lean:119](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/AxiomCMaximality.lean#L119))。
这些定理本身是 W1，但所属模块的**整体定位**是候选（§7）。

---

## 4. 条件档（W2 / W3，必须带前提）

> 前提原样抄写。去掉前提即不成立，反例位置已标。

### 4.1 `no_determiner`（母定理，W2）

[IndependenceCheck.lean:209](file:///D:/CSQIT-v23-fix/CSQIT_W1/IndependenceCheck.lean#L209)：

```
theorem no_determiner {V P : Type} (model : P → FieldValueModel V)
    (h_fields : ∀ p q : P, (model p).1 = (model q).1)
    (p₁ p₂ : P) (h_values : (model p₁).2 ≠ (model p₂).2) :
    ¬ ∃ f : CompilerAxiom ℕ ℕ → V, ∀ p : P, f (model p).1 = (model p).2
```

前提：`h_fields`（族内五字段相同）+ `p₁ p₂` + `h_values`（两点取值不同）。
结论：不存在从五字段到该数值的决定函数。**它的 8 个实例是 W1 闭式**（见 §3.2 与 TSV），
因为实例把前提全部实例化了。引用「五字段不决定 X」时，引实例，不要引母定理。

### 4.2 带显式前提的唯一性定理（W2）

| 定理 | 位置 | 前提（原样） | 换掉前提的反例 |
|---|---|---|---|
| `forty_two_unique_of_base` | [IndependenceCheck.lean:356](file:///D:/CSQIT-v23-fix/CSQIT_W1/IndependenceCheck.lean#L356) | `h₁ : B.p1 = 2`、`h₂ : B.p2 = 3`、`h₃ : B.p3 = 5`、`h₄ : B.p4 = 7` | `identity_42_fails_on_altBase`（:484，换基底则 42 失效） |
| `one_o_five_unique_of_base` | :365 | `h₂ : B.p2 = 3`、`h₃ : B.p3 = 5`、`h₄ : B.p4 = 7` | 同上换基底 |
| `two_eighty_nine_unique_of_base` | :373 | `h₁…h₄` 全四个 | 同上 |
| `eight_unique_of_base` | :383 | `h₁ : B.p1 = 2` | 同上 |
| `eight_forty_unique_of_orders` | :391 | `h₄ : g4 = 12`、`h₅ : g5 = 60`、`h₇ : g7 = 168` | 换群阶则 `lcm ≠ 840` |
| `totalClosure_unique_of_orders` | :404 | 同上三式 | 换群阶则 `≠ 420` |
| `base_uniqueness_by_exclusion` | [SequenceStructure.lean:467](file:///D:/CSQIT-v23-fix/CSQIT_W1/SequenceStructure.lean#L467) | `h1 : MUST_HAVE ⊆ B`、`h2 : B ⊆ MUST_HAVE` | `h2` 即「无冗余」前提；去掉则 `B = {2,3,5,7,11}` 亦满足 `h1` |
| `unique_base_is_2357` | :475 | 同上两式 | 同上 |
| `attractor_unique` | [AttractorPrototype.lean:138](file:///D:/CSQIT-v23-fix/CSQIT_W1/AttractorPrototype.lean#L138) | 公式形式 + 递增素数约束（见定理签名） | 换公式形式则唯一性不成立 |
| `conditional_order` | [OrderAndFixedPoint.lean:87](file:///D:/CSQIT-v23-fix/CSQIT_V1Bridge/OrderAndFixedPoint.lean#L87) | `h : ∀ x y, CA.compose x y ≠ x` | 左投影模型违反 `h`（`leftProjection`） |
| `alpha_inv_absolute_error_bounded` | [ObserverLayering.lean:197](file:///D:/CSQIT-v23-fix/CSQIT_W1/ObserverLayering.lean#L197) | `h_obs : observed_energy … = 137.035999206`（CODATA 2018） | 去掉 `h_obs` 则误差界无意义 |
| `omega_Lambda_encoding_unique_of_base` | [IndependenceCheck.lean:419](file:///D:/CSQIT-v23-fix/CSQIT_W1/IndependenceCheck.lean#L419) | `hB : e1 B = 17`（W3：把 `289/420` 当作暗能量份额） | 数值本身不依赖 `hB` 之外的物理诠释；物理解释无定理 |

### 4.3 W3（诠释层，不得当数学结论引用）

- `weaver_radial_at_alpha_level`（[ObserverLayering.lean:118](file:///D:/CSQIT-v23-fix/CSQIT_W1/ObserverLayering.lean#L118)）
- `cp_phase_at_alpha_level`（:129）
- `observed_equals_bare_at_alpha_level`（:151）
- `omega_Lambda_encoding_unique_of_base`（:419）

这些是「在 Weaver 修正/暗能量份额诠释下」的陈述。代数部分可单独引用，
**「裸值 = 观测值」「289/420 就是暗能量密度」不得作为数学结论**。

---

## 5. 外部输入（不是推导出来的）

> 判据：数值不出自任何 `class` 字段，也不出自任何已证定理的结论；
> 它以字面 `def` 或定理前提的形式进入代码。

| # | 外部输入 | 从哪进入代码 | 性质 | 「依赖它」意味着 |
|---|---|---|---|---|
| E1 | 素基底 `{2,3,5,7}` | `Foundation.lean:130-133` 四个字面 `def p1…p4`；`MinimalCost.lean:76` `def mkBase` | `def:mkBase` | 所有 42/105/289/137.036/250-9 的数值都与该字面基底绑定；换基底数值即变，公理照常成立（`alpha_inv_not_determined_by_fields` 等） |
| E2 | 群阶 `12 / 60 / 168` | `Foundation.lean:108-110` 字面 `def A4_order / A5_order / PSL27_order` | `def:totalClosure` | 420/840 是这三个字面数的 `lcm` 计算；三群阶不被五字段决定（`order12/60/168_not_determined_by_fields`） |
| E3 | `lcm/2` 规则 | `Foundation.lean:114` `Nat.lcm (Nat.lcm A4 A5) PSL / 2` | `def:totalClosure` | 「除以 2」是定义选择，无公理依据；换规则则 420 变（`closure_not_determined_by_fields` 的换参证据） |
| E4 | `8` 与 `64` | `Foundation.lean:567` `closure_sequence_extended` 字面 `match` | `def:closure_sequence` | 前两项是写死的字面项，不是推导值（`level64_not_determined_by_fields`） |
| E5 | `250/9` | `Foundation.lean:148` `def observerBridge` 的闭式 | `def:observerBridge` | 公式是定义选择；`bridge_not_determined_by_fields` 证明它不被五字段决定 |
| E6 | `30 / 61`（H₀） | `Foundation.lean:161-162` `def hubbleConstant := inverseFineStructure * 30 / 61` | `external:H0` | `30`、`61` 不在基底 P 中，是框架外常数（`hubble_not_determined_by_fields`；`hubbleModel` :430 把槽位参数化） |
| E7 | CODATA `137.035999206` | `ObserverLayering.lean:197` 定理前提 `h_obs` | `external:CODATA` | **只以定理前提出现**，不进任何 `def`；去掉前提，误差界定理不成立 |
| E8 | 观测 H₀ ≈ 67.4 | 无定理；仅 `hubbleConstant` 的注释叙事 | `external:H0` | 「H₀ = 67.4 与观测一致」不是定理；只有 `hubbleConstant_eq` 的代数恒等式 |
| E9 | Ω_Λ/Planck 对应 | 无定理；仅 `289/420` 编码值 | `external:Planck` | 「289/420 是暗能量密度」未形式化（CLAIMS_LEDGER C6） |

**统一口径**：外部输入不使定理变「假」，但使定理的**适用范围**从「数学必然」降为
「在该输入取值下为真」。引用时必须写出输入名，例如
「在 `def:mkBase = (2,3,5,7)` 下，`e₁²−e₃ = 42`」。

---

## 6. 已证否 / 禁止使用（禁令）

> 本节是禁令，不是备注。以下命题**不得**作为前提、论据或「已知结果」出现在任何后续工作中。

1. **禁止**说「`{2,3,5,7}` 是唯一素基底」。
   证否：`prime_solution_lex_min`（只是素数类字典序最小）、`solsUpTo_12_eq`（`[1,12]⁴` 内 36 解）、
   `vieta_partner`（全局解集无穷）、`no_determiner`。
2. **禁止**说「420 / 闭包序列由公理推出」。
   证否：`closure_not_determined_by_fields`；`totalClosure` 是字面 `lcm/2` 定义（`Foundation.lean:114`）。
3. **禁止**说「α⁻¹ 有两条独立推导」。
   证否：`alpha_inv_exact_eq_inverseFineStructure` 为 `rfl`；`declaration_alpha_inv_consistency`
   是同一闭式的两种编码。这是编码一致性，不是独立推导。
4. **禁止**说「A–J（A–K）形式化了离散因果」。
   证否：`base_input_empty`、`enhanced_input_empty` 强制 `input ≡ []`；
   `base_weaving_vacuous`、`enhanced_weaving_vacuous` 使 input 层编织前提恒假。
   仅 output 层 `AxiomD'.op_weaving` 非空洞（`fin7_opweaving_nonvacuous`，:129）。
5. **禁止**说「`curvature_energy` 严格递减」。
   证否：`curvature_energy_not_strict_decreasing`、`curvature_energy_counterexample`。
   「`n ≥ 8` 递减」只是分析性论证，未形式化。
6. **禁止**说「旧 `GenerationBridge` 可编译 / 已修复」。
   事实：原 1948 行从未编译通过，已退役；现 65 行墓碑含 4 条数论定理并参与构建。
7. **禁止**说「全项目 451 条定理 / 28 模块 / 恰好一个 sorry」。
   事实：474 条 theorem/lemma、29 个命题模块（+4 增强）、构建内零 sorry、无 `axiom` 声明。
8. **禁止**说「五个定义选择就是全部外部依赖」。
   证否：H₀ 的 `30/61` 与 CODATA `137.035999206` 是框架外输入（§5 E6/E7）。
9. **禁止**把「塔的每层携带不同依赖/规则」当前提。
   证否：`core_collapse` + `layer_input_empty` + `top_input_empty`：每层与塔顶 `input ≡ []`，
   且所有层是同一环境模型的限制，公理字段全部继承。
10. **禁止**把「塔顶自动存在且自动最大」当前提。
    证否：G44 族（§3.3）；`pairTower_top_no_maximal_order`（§3.5，W1 反例）。
11. **禁止**把「引力 / 势由 `AxiomA` + `AxiomC` 导出」当前提。
    事实：两套字段表中**没有**势/度规/曲率字段（§2.1–§2.3 已逐字段核对）；
    `AdditivePotential` 只是接口，且零势恒存在，非零势的数值不被任何字段决定
    （`witness_potential_not_determined_by_fields`，[Potential.lean:192](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Potential.lean#L192)）。
12. **禁止**把「42/105/289 是从公理算出来的」当前提。
    正确表述见 §0.2 与 §5 E1：它们在该字面 `def` 下为真，五字段不决定它们。

---

## 7. 候选而非基座

> 判据：模块整体未进入「474 条基线」的审计链，或其主要内容是接口/设计；
> 只能引用其中**已机检的具体定理**，不能引用模块的「整体叙事」。

### 7.1 `CSQIT_LayerTower`（4 模块 / 62 声明）

- **已验（可引用具体定理）**：层是闭子模型、层间嵌入、塔顶 `Set` 并是余极限、
  `AxiomA`/`AxiomC` 由限制继承、逐层 `input ≡ []`、见证塔顶无不动点/无自生成满射、
  `AxiomC` 世界的 G44 反向边实例。
- **只是接口**：`AdditivePotential`（[Potential.lean:42](file:///D:/CSQIT-v23-fix/CSQIT_LayerTower/Potential.lean#L42)）——
  势的载体已参数化，但「力/引力」语义没有任何定理；零势恒存在。
- **未落地**：逐层「新增公理」、逐层「不同规则」、operad 层面的塔余极限。
- **可引用程度**：具体定理可引；**不得**引用为「CSQIT 已形式化分层引力」。

### 7.2 `CSQIT_LayerCuts`（1 模块 / 20 声明）

- **已验**：`pathLapForm` 非负、零模 ⟺ 常函数、零点集与正权取值无关；
  压缩比秩–零度互补、`ker = ⊥ ⟺ r = 1`、`ker ≠ ⊥ ⟺ r < 1`；
  `flowAmplitude_layerInvariant_iff`（振幅沿流恒常 ⟺ 初值为 1）；
  `no_amplitude_factorization_of_not_injective`（非单射粗粒化必改振幅）。
- **只是定义**：`compressionRatio`、`effectiveDim`、`LayerInvariant`。
- **未落地**：数值谱隙（只做了零点集）、随尺度参数化的 `P_s` 族、
  「层界 = 零点集」「压缩比 = 层间距离」的诠释（C 档）。
- **可引用程度**：B 档骨架可引；A 档否定式（`flowAmplitude_layerInvariant_iff`、
  `no_amplitude_factorization_of_not_injective`）可引；**不得**引用为「能隙已算出」。

### 7.3 `CSQIT_V1Bridge`（24 roots）

- **已验（可引用）**：全部 no-go（§3.3）、刚性/桥接（§3.4）、见证模型与 `Fin n` 模型。
- **定位**：这是**接口检验层**——把 V1.0→V7.1.1 的主张翻译成 `AxiomA`/`AxiomC` 模型内的
  否定定理或存在性定理。它证明的是「某主张在最小代数翻译下不成立/成立」，
  **不是**原主张的整体证否。
- **可引用程度**：定理级可引；引用时必须写「在 `AxiomA`/`AxiomC` 模型内」或
  「在最小代数翻译下」。不得把 §3.3 的 no-go 扩大为「宇宙论已证否」。

### 7.4 `CSQIT_Enhanced`

- **已验（可引用）**：`base_input_empty`、`enhanced_input_empty`、
  `base_weaving_vacuous`、`enhanced_weaving_vacuous`；
  output 层非空洞见证 `fin7_opweaving_nonvacuous`（[Bridge.lean:129](file:///D:/CSQIT-v23-fix/CSQIT_Enhanced/Bridge.lean#L129)）。
- **定位**：v11.2.8 的完整公理移植（`AxiomA'`/`AxiomB'`/`AxiomC'`/`AxiomD'` 等）。
  其中 input 层因果公理**全部空洞**；唯一非空洞的是 output 层 `AxiomD'.op_weaving`。
- **可引用程度**：坍缩类结论可引；**不得**引用为「A–J 已形式化」。

---

## 8. 未形式化清单（逐条，不合并）

> 标准：论文/文档/注释里说过，但代码里**没有对应定理名**。每条给出处与现状。

| # | 断言 | 出处 | 现状 |
|---|---|---|---|
| U1 | 「唯一素基底 `{2,3,5,7}`」 | 论文 EN:48/141-143；ZH:39/68 | 无支撑；被 `prime_solution_lex_min`、`solsUpTo_12_eq`、`vieta_partner` 反驳 |
| U2 | 「420 / 闭包序列由公理推出」 | README 系列；EN:48 | 无支撑；被 `closure_not_determined_by_fields` 反驳 |
| U3 | 「α⁻¹ 两条独立推导收敛到同一值」 | cover letter:62-63 | 无支撑；`alpha_inv_exact_eq_inverseFineStructure` 为 `rfl` |
| U4 | 「A–J 形式化了离散因果」 | BRIDGE_COMPILER.md:10 | 无支撑；input 层编织前提恒假 |
| U5 | 「旧 GenerationBridge 可编译」 | v17–v23 历史表述 | 假；原模块从未编译通过 |
| U6 | 「curvature_energy 严格递减」 | v12/GB 历史表述 | 假；有形式化反例 |
| U7 | 「所有结果都已形式化」 | 论文 EN:531-532；ZH:365-368 | 部分假：§5.2/§5.3 两个必要性反例只在注释（`AxiomIndependence.lean:83-149`），无定理名 |
| U8 | 「451 条定理 / 28 模块 / 恰好一个 sorry」 | 论文 EN:533-540、613-623；ZH:368、434 | 计数过时；实测 474 / 29(+4) / 构建内零 sorry |
| U9 | 「GB 未修复且当前无法编译」 | 论文 EN:598-607；ZH:422-428 | 就现仓库为假（墓碑参与构建、0 错误） |
| U10 | 「五个定义选择就是全部外部依赖」 | 论文 EN:875-885；ZH:602-603 | 假；H₀ 30/61 与 CODATA 另计 |
| U11 | 「`289/420` 是暗能量密度占比」 | 论文 Ω_Λ 段 | 无物理定理；只有编码恒等式，Planck 对应未形式化 |
| U12 | 「H₀ ≈ 67.4 与观测一致」 | 注释叙事；`Foundation.lean:160` | 无定理；`30/61` 是外部拟合常数 |
| U13 | 「α⁻¹ 裸值 = 观测值」 | `ObserverLayering.lean:151` 注释 | 只有 W3 诠释定理；物理对应未形式化 |
| U14 | 「能隙数值 / 谱隙」 | `CSQIT_LayerCuts/Cuts.lean` 头注 | 只形式化了零点集；最小非零特征值未做 |
| U15 | 「压缩比 = 层间距离」 | 同上 | `compressionRatio` 只是定义；无尺度族 `P_s` |
| U16 | 「塔每层携带不同依赖/规则」 | `CSQIT_LayerTower/DESIGN.md` 叙事 | 被 `layer_input_empty`/`top_input_empty` 否定；只能分层载体与振幅值 |
| U17 | 「塔顶自动存在且自动最大」 | 同上 | 被 G44 族与 `pairTower_top_no_maximal_order` 否定 |
| U18 | 「引力 / 势由现有公理导出」 | 同上 §0 | 无字段；`AdditivePotential` 仅接口，零势恒存在 |
| U19 | 「RG 流已证否」 | V1Bridge §8 边界注记 | 只否定了振幅层最小实现；A2 整体仍 C |
| U20 | 「全息原理已证否」 | 同上 | 只否定 v23 唯一 `input` 通道上的实现；A1 整体仍 C |
| U21 | 「因果性不存在」 | 同上 | 只说明线性全局时间不被强制；B 档 |
| U22 | 「A5 测度刚性」 | 同上 | 无进展，仍 C |
| U23 | 「A2 原生 operad 语义已证否」 | `OperadImpossibility.lean:191-192` | 只覆盖一元翻译；原生语义仍 C |
| U24 | 「operad 层面的塔余极限」 | `DESIGN.md` §1.3 | 无 operad 对象；C 档 |
| U25 | 「`n ≥ 8` 时 curvature_energy 递减」 | `GenerationBridge.lean` 头注分析 | 分析性论证，未形式化 |
| U26 | 「两个必要性反例（次可加失败 / 去 Nodup 失败）」 | `AxiomIndependence.lean:83-149`（仅注释） | 无定理名 |

---

## 9. 机器可读清单字段说明

`foundation_base.tsv` 为 UTF-8、Tab 分隔，首行表头：

| 列 | 取值域 | 说明 |
|---|---|---|
| `theorem` | Lean 短名 | 与源码一致 |
| `location` | `相对路径:行号` | 行号为声明行 |
| `tier` | `W1` / `W2` / `W3` / `DENIED` / `CANDIDATE` | 见 §0.1 |
| `axioms` | `std3` / `propext+quot` / `propext` / `none` / `n/a` | 全部来自逐条 `#print axioms` 实测（§1.3）；`std3 = propext+Classical.choice+Quot.sound`；`propext+quot = propext+Quot.sound`；`none` = 不依赖任何公理；`n/a` = 非定理声明。表内**不存在**任何带 `*` 的上界值 |
| `basis` | `axioms` / `def:<名字>` / `external:<来源>` | 见 §0.1 |
| `premises` | `none` 或短标签 | 如 `base=2,3,5,7`、`orders=12/60/168`、`h_obs=CODATA` |
| `unconditional` | `yes` / `no` | 判据：陈述里有没有自由参数 |

自动核对建议：
1. 对每行执行 `#print axioms <全名>`，比对 `axioms` 列；
2. 用 `grep -n` 核 `location` 列的行号是否仍指向该声明；
3. `tier=DENIED` 的行不得出现在任何 `premises` 列中。
