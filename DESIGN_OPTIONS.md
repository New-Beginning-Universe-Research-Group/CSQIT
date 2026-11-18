# DESIGN_OPTIONS · 重构 Core Collapse 公理的方案分析

> 状态：**只读分析，不修改源码，不 commit 代码改动**（本文件可 commit）。
> 日期：2026-11-05。
> 前提事实（已形式化，见 `CSQIT_Enhanced/Bridge.lean`、`CSQIT_W1/CoreCollapse.lean`、`CSQIT_W1/AxiomIndependence.lean`）：
> - `core_collapse`（三版独立证明）：`compose_input + input_nodup` 强制 `input α ≡ []`。
> - `weaving_axiom` / `weaving_axiom'` 前提因 `input ≡ []` 恒假。
> - v11.2.8 注释自述"增强版（A′–J′）修复了空洞"——实际只修复了 `op_weaving`（output 层），input 层仍空洞。

---

## 任务 1：依赖测绘

### 1.1 直接/间接引用 `compose_input` 与 `input_nodup` 的定理清单

按文件分组。每条标注"删字段后失效 / 可重述 / 不受影响"。

#### A. `CompilerAxioms.lean`（v23 主体系）
| 定理名 | 类型 | 依赖性质 | 删字段后 |
|---|---|---|---|
| `core_collapse` (:127) | 坍缩根定理 | 直接用 `compose_input` + `input_nodup` | **失效**（坍缩第一步消失） |
| `core_collapse_length_zero` (:144) | 推论 | 间接：`rw [core_collapse]` | **失效** |
| `no_dependency` (:151) | 推论 | 间接：`rw [core_collapse]` | **失效** |
| `no_nonempty_dependency` (:156) | 推论 | 间接：`intro h; rcases h with ... exact no_dependency ...` | **失效** |
| `core_collapse_independent_of_output` (:190) | 总结 | 间接：`exact core_collapse` | **失效** |
| `compiler_theorem_summary` (:211) | 汇总 | 间接引用以上所有 | **失效** |
| **subtotal** | **6 条** | | **6 条失效** |

#### B. `CoreCollapse.lean`（Foundation.AxiomA 版本）
| 定理名 | 类型 | 依赖性质 | 删字段后 |
|---|---|---|---|
| `input_must_be_empty` (:56) | 坍缩根定理 | 直接用 `compose_input` + `input_nodup` | **失效** |
| `input_length_zero` (:73) | 推论 | 间接：`rw [input_must_be_empty]` | **失效** |
| `no_causal_input` (:81) | 推论 | 间接：`rw [input_must_be_empty]` | **失效** |
| `no_satisfiable_weaving_premise` (:85) | 推论 | 间接：`intro h; rcases ... exact input_must_be_empty ...` | **失效** |
| `axiomD_weaving_premise_false` (:107) | AxiomD 冗余 | 间接：`rw [input_length_zero]` 得出 `0 = 0 + 1` 矛盾 | **失效** |
| `hypothetical_weaving_axiom_equivalent_to_true` (:115) | weaving 空洞 | 间接：`no_causal_input` 使前提恒假 | **失效** |
| `core_collapse_summary` (:148) | 综合结论 | 间接引用以上所有 | **失效** |
| `output_compose_is_right` (:135) | output 退化引理 | 只用 `compose_output`（另一字段，与 compose_input/input_nodup 无关） | **不受影响** |
| **subtotal** | **8 条** | | **7 条失效，1 条不受影响** |

#### C. `CSQIT_Enhanced/Bridge.lean`（增强体系）
| 定理名 | 类型 | 依赖性质 | 删字段后 |
|---|---|---|---|
| `base_input_empty` (:37) | 坍缩根（AxiomA 版） | 直接用 `compose_input` + `input_nodup` | **失效** |
| `base_weaving_vacuous` (:59) | weaving 空洞（AxiomB 版） | 间接：`rw [base_input_empty α]; simp` | **失效** |
| `base_weaving_premise_never` (:65) | weaving 存在否定 | 间接：`base_weaving_vacuous` | **失效** |
| `enhanced_input_empty` (:72) | 坍缩根（AxiomA' 版） | 直接用 `compose_input` + `input_nodup` | **失效** |
| `enhanced_weaving_vacuous` (:97) | weaving 空洞（AxiomB' 版） | 间接：`rw [enhanced_input_empty]; simp` | **失效** |
| `enhanced_weaving_premise_never` (:103) | weaving 存在否定 | 间接：`enhanced_weaving_vacuous` | **失效** |
| `fin7_opweaving_premise_witness` (:116) | op_weaving 见证（output 层） | 不依赖 input 字段，只用 `output` + `lt` | **不受影响** |
| `fin7_opweaving_conclusion_witness` (:123) | 同上 | 同上 | **不受影响** |
| `fin7_opweaving_nonvacuous` (:129) | 构造性存在见证 | 同上 | **不受影响** |
| `compilerOfAxiomA` (:152) | 投影 def | 直接取 `input / compose_input / input_nodup` 等字段 | 投影函数本身存在，但投影后的公理类性质随字段变化 |
| `instCompilerOfAxiomA` (:160) | 投影 instance | 同上 | 同上 |
| `projection_fields_eq` (:165) | 逐字段 rfl 相等 | 同上 | 同上 |
| `projection_drops_output` (:175) | 投影丢弃声明 | 同上 | 同上 |
| **subtotal** | **13 条** | | **6 条失效，3 条不受影响，4 条随字段变化** |

#### D. `AxiomIndependence.lean`（独立测试模块）
| 定理名 | 类型 | 删字段后 |
|---|---|---|
| `MinimalCompilerAxiom` (:53) | 简化类定义（去掉 assoc，保留另外 4 条） | 类定义本身存在，但坍缩证明依赖被删掉的字段 |
| `minimal_core_collapse` (:65) | 在 Minimal 中证明坍缩 | **失效**（直接用 compose_input + input_nodup） |
| 反例注释（§2:次可加 compose_input + input_nodup → 坍缩失败） | 事实 | 变成我们路线的正例 |
| 分析注释（§3:去掉 input_nodup → 坍缩无法开始） | 事实 | 同上 |
| **subtotal** | | **1 条失效，其余变正例** |

#### 总计
| 分类 | 数量 | 占比 |
|---|---|---|
| 删字段后失效 | 20 条 | 59% |
| 不受影响 | 4 条 | 12% |
| 投影函数（随字段变化但不消失） | 4 条 | 12% |
| 独立测试（变正例） | 5 条（注释为主） | 15% |
| **总计** | **≈ 33 条**（不含注释） | **100%** |

**关键观察**：失效的 20 条定理构成一个**单一的坍缩链条**——从 `compose_input + input_nodup` 出发，经过多层 `rw` 传递到所有 weaving 空洞定理。没有独立的下游分支（除了 `AxiomD` 冗余，它也是坍缩的直接推论）。**这意味着坍缩是一个高度集中的局部问题，不是大范围渗透。**

### 1.2 传递依赖扫描（全量 474 定理）
扫描范围：`CSQIT_W1/*.lean` 全部 theorem/lemma 的 `#print axioms` 输出（见 `analysis_axioms.tsv`，474/474 条）。

**结论**：
- 没有任何**其他模块的定理**（Foundation、QuantumCorrection、ObserverLayering、PhysicalConnect 等）引用 core_collapse 或其任何推论。
- 坍缩链条完全封闭在 CompilerAxioms + CoreCollapse + Bridge + AxiomIndependence 四个模块内。
- 这意味着动 `compose_input` / `input_nodup` **不会影响 474 条主体系定理的其余部分**——它们的依赖图和坍缩链条是**完全独立**的。

### 1.3 `core_collapse` 是否为根
**是**。坍缩链条的**唯一前提**是 `compose_input` + `input_nodup`（`compose` 只是类型载体，`compose_assoc` 已证明冗余，见 `minimal_core_collapse`）。坍缩链条的**所有后续定理**（长度零、无依赖、weaving 空洞、AxiomD 冗余）都是这个根的直接或间接推论。**砍掉根，整条链倒下，没有独立的下游定理**。

---

## 任务 2：两条路线的具体形态

### 路线一：放宽 `input_nodup`（改或删）

#### 方案 1A：直接删除 `input_nodup` 字段
**改动**：CompilerAxiom / AxiomA / AxiomA' 都去掉 `input_nodup : ∀ α, (input α).Nodup`。
**坍缩证明链失效点**：第一步 `(input(compose α α)).Nodup := input_nodup (compose α α)` 消失。矛盾的核心证据不存在。
**非空模型验证（纸面 + 可验算）**：
> 载体：C = ℕ（自然数加法群），M = ℕ。
> compose m n = m + n（加法，结合律成立）。
> input n = List.replicate n 0（n 个 0 的重复列表）。
> 字段检查：
> - `input_nodup`：**已删除，无需检查**。
> - `compose_input`：`input(m+n) = List.replicate(m+n) 0 = (List.replicate m 0) ++ (List.replicate n 0) = input m ++ input n` ✅（List.replicate 的 ++ 结合性）。
> - `compose_assoc`：加法结合律 ✅。
> - **input 非空**：当 n > 0 时，`input n` 有 n 个元素 ✅。
> - **weaving 前提非空**：取 AxiomA' + AxiomB'，output α = α（恒等），lt = `<`（自然数标准序）。AxiomB'.weaving_axiom' 的前提：`x ∈ input α`，结论：`x < output α`。取 α = 5，x = 0（0 ∈ input 5 因为 input 5 = [0,0,0,0,0]），结论 `0 < 5` ✅。
> - **op_weaving 前提也非空**：取 α=2, β=5, γ=3。`output α = 2 < 5 = output β` ✅，`compose α γ = 2 + 3 = 5 = β` ✅。
> - **Finite 性**：`localFinite_past {x | y < x}` 对 x ∈ ℕ 是无限的 ❌——但这是 AxiomB 的字段要求，不是 input 字段的问题。我们可以把 lt 改成有限集上的序（比如 Fin N），或者局部有限只要求过去的有限段有限。

#### 方案 1B：弱化 `input_nodup` 为"至多重复一次"
**改动**：`input_nodup_at_most_twice : ∀ α y, count y (input α) ≤ 2`（同一元素在列表中最多出现 2 次）。
**坍缩证明链失效点**：原来矛盾来自 `(L ++ L).Nodup → L = []`，现在 `(L ++ L)` 中同一元素出现 4 次，不满足"至多一次"但满足"至多两次"的弱化版本，矛盾消失。
**非空模型**：同样用方案 1A 的模型（input n 有 n 个重复的 0），`count 0 (input n) = n`。当 n ≤ 2 时满足"至多两次"，n > 2 时不满足。所以只在小 n 上成立，大 n 仍坍缩。**不够好，建议 1A 或 2。**

#### 方案 1C：保留 `input_nodup` 但只对"最大对象"成立
**改动**：`input_nodup_max : ∀ α ∈ max_set, (input α).Nodup`——其中 max_set 是 C 中满足某种最大性条件的集合（比如 `compose α β = α` 对所有 β）。
**坍缩证明链失效点**：对非最大对象，`input_nodup` 不适用，矛盾不出现。
**非空模型**：大部分 α 的 input 可以非空，只有 max_set 中的 α 仍坍缩。
**风险**：max_set 的定义引入了额外结构（C 上的偏序或等价类），这是未经检验的假设。

### 路线二：改 `compose_input` 的语义

#### 方案 2A：`input(compose α β) = input β`（取右元）
**改动**：CompilerAxiom / AxiomA / AxiomA' 都把 `compose_input : ∀ α β, input(compose α β) = input α ++ input β` 改成 `compose_input : ∀ α β, input(compose α β) = input β`。
**坍缩证明链失效点**：第一步 `input(compose α α) = input α ++ input α` 变成 `input(compose α α) = input α`。`(input(compose α α)).Nodup` 仍成立（来自 input_nodup），但推不出 `(input α ++ input α).Nodup`——因为 `input(compose α α) = input α`，不是 `input α ++ input α`。所以矛盾消失。
**compose_assoc 是否还成立**？AxiomA' 中 `compose_assoc : ∀ α β γ, compose(compose α β) γ = compose α (compose β γ)` 是 `compose` 函数的性质，与 `input` 无关——它**仍成立**（只要 compose 本身结合）。`compose_input` 只是 input 字段和 compose 的关系，改它不影响 compose_assoc。
**非空模型验证**：
> C = ℕ, M = ℕ, compose m n = m + n, input n = [n]（单元素列表，Nodup ✅）。
> - `compose_input`：`input(m+n) = [m+n]`，但 `input β = input n = [n]`——**不相等！**
> 改 compose 为左投影：compose m n = m（左边优先）。
> - `compose_input`：`input(compose α β) = input α`（而不是 input β）。
> - 哦对，方案 2A 是取右元，所以 compose 应该是右投影：compose m n = n。
> - `input(compose α β) = input β = [β]` ✅；`input(compose(compose α β) γ) = input(compose β γ) = input γ = [γ]`；`input(compose α (compose β γ)) = input(compose β γ) = [γ]` ✅——compose_assoc 成立。
> - **input_nodup**：`input α = [α]`，Nodup ✅（无重复）。
> - **compose_assoc**：compose(compose α β) γ = compose β γ = γ = compose α (compose β γ) ✅。
> - **weaving 前提非空**：取 AxiomA' + AxiomB'，output α = α，lt = `<`。取 α=5, x=5（5 ∈ [5] = input 5），结论 `5 < 5` ❌。取 lt 为严格序，output α = α + 1，α=5, x=5，结论 `5 < 6` ✅。
> - **Finite 性**：ℕ 上局部有限 Past 无限——同样的问题。

#### 方案 2B：`input(compose α β) = input α`（取左元）
与 2A 对称。compose 改为左投影 m n = m。其余相同。**等价于 2A，只需决定取左还是取右。**

#### 方案 2C：`input(compose α β) = (input α ++ input β).dedup`（去重拼接）
**坍缩证明链失效点**：原来 `(L ++ L).Nodup → L = []` 的矛盾现在变成 `(L ++ L).dedup).Nodup → L.dedup = []`，只推出 L 中无元素，即 `input α = []`——**坍缩仍成立！** 因为 dedup 去掉重复后，如果原列表有重复元素，dedup 仍非空；但坍缩中我们考虑的是相同列表拼接，dedup 后是 dedup(L)。矛盾链变成 `(dedup(L ++ L)).Nodup ↔ dedup(L).Nodup`——这**不推不出 L = []**，但也不允许 L 有重复元素。

等一下，重新分析：`input(compose α α) = dedup(input α ++ input α) = dedup(input α)`（因为 ++ 把相同列表拼起来，dedup 后等于 dedup(input α)）。`input_nodup` 要求 `dedup(input α)).Nodup`——这**总是成立**，因为 dedup 后不会有重复！所以矛盾完全消失！

**但 dedup 会丢信息**：如果 input α = [0, 0]（有重复），dedup 后 = [0]。`input(compose α α) = [0]`，`input(compose α α)` 的 Nodup 检查通过。**非空 input 合法！**

**compose_assoc**：`dedup(input(compose(compose α β) γ)) = dedup(input(compose β γ)) = dedup(input(β) ++ input(γ))`（dedup 后）；`dedup(input(compose α (compose β γ))) = dedup(input α ++ input(compose β γ)) = dedup(input α ++ dedup(input β ++ input γ))`。**dedup 与 ++ 不交换**：`dedup([0,0] ++ [0,0]) = dedup([0,0,0,0]) = [0]`，但 `dedup([0,0]) ++ dedup([0,0]) = [0] ++ [0] = [0,0]`，dedup 后 = [0]——**结果相同**。一般地，`dedup(x ++ y) = dedup(dedup(x) ++ dedup(y))` ✅。所以 compose_assoc 仍成立。

**非空模型**：任何 input 函数，只要 dedup 后非空就行。比如 input n = [n]（Nodup），dedup 后仍非空 ✅。input n = [n, n]（非 Nodup），dedup 后 = [n] 非空 ✅。

### 关键卡住点（AxiomB/AxiomB' 其余字段检查）
AxiomB/AxiomB' 有 9 个字段：le, lt, le_refl, le_trans, le_antisymm, lt_iff_le_not_le, localFinite_past, localFinite_future, weaving_axiom。

**方案 1A/2A/2C 都能让 weaving 前提非空**，但：
- `localFinite_past` / `localFinite_future`：要求 `< y` 的元素个数有限。如果 M = ℕ，取 lt = `<`（标准序），过去 {x | x < y} = {0, 1, ..., y-1}，有限 ✅！哦，我之前说反了——过去是有限的（对每个 y 只有有限个 x < y），未来 {x | y < x} 才是无限的。
- 如果 M = Fin N，过去和未来都是有限的 ✅。
- 所以 **localFinite 可以满足**，只要 M 有限（取 Fin 7 或 Fin 8），或者 lt 是有限秩偏序。

**结论**：去掉 input_nodup（方案 1A）或改 compose_input 语义（方案 2A/2B/2C）**都能让 weaving 前提非空**，不需要额外改 AxiomB/AxiomB' 的其余字段。

---

## 任务 3：决策表

### 6 个候选方案

| # | 方案 | 改动字段 | 受影响定理数 | weaving 能否非空 | compose_assoc 是否保留 | compose_assoc 是否必需 | 实现难度 | 一句话代价 |
|---|---|---|---|---|---|---|---|---|
| 1 | **冻结（不改）** | 无 | 0 | **不能**（input ≡ []，weaving 前提恒假） | ✅ 保留 | ✅ 必需（v23 主体系依赖） | 零 | **代价是放弃 input 层因果表达**，只能做 output 层编织 |
| 2 | 1A：删 `input_nodup` | CompilerAxiom/AxiomA/AxiomA' 都去掉 `input_nodup` | **20 条失效**（坍缩根 + 所有推论） | ✅ 能（非空 input 合法，weaving 前提可非空） | ✅ 保留（不动 compose 字段） | ✅ 必需 | **低**（删一行字段 + 删坍缩证明） | **代价是 `AxiomA → CompilerAxiom` 投影丢失 `input_nodup`，现有 no_determiner 实例（instNatAdd/Left）不变** |
| 3 | 1C：`input_nodup` 只对最大对象 | 加 max_set 定义 + 改字段范围 | ~22 条 | 部分非空（只有非最大对象） | ✅ 保留 | ✅ 必需 | 中（需定义 max_set 结构并验证性质） | **代价是引入额外结构假设，max_set 定义未经检验** |
| 4 | 2A：`compose_input` 取右元 | 改 `∀ α β, input(compose α β) = input β` | **20 条失效** | ✅ 能（input 非空合法，weaving 前提可非空） | ✅ 保留 | ⚠️ 不再必需（compose 是右投影后结合律仍成立但不再是必然） | 低（改一行等式 + 删坍缩证明） | **代价是 compose 函数必须是右投影，compose 的代数结构被削弱，compose_assoc 保留但变成冗余** |
| 5 | 2B：`compose_input` 取左元 | 改 `∀ α β, input(compose α β) = input α` | **20 条失效** | ✅ 能 | ✅ 保留 | ⚠️ 同上 | 低 | **等价于 2A，只是取左而非取右** |
| 6 | 2C：`compose_input` 去重拼接 | 改 `input(compose α β) = (input α ++ input β).dedup` | **20 条失效** | ✅ 能 | ✅ 保留 | ✅ 必需（dedup 与 ++ 结合性成立） | 低（改一行等式 + 删坍缩证明） | **代价是 dedup 丢失重复信息，物理上重复依赖是否有意义** |

### 推荐方案：**2C（`compose_input` 去重拼接）**

**推荐理由**：
1. **坍缩自然消解**：原来精确等式 `input(compose α α) = input α ++ input α` 配合 Nodup 推矛盾；去重后 `input(compose α α) = dedup(input α ++ input α) = dedup(input α)`，Nodup 检查变成 `(dedup(input α)).Nodup`——**dedup 后自动满足 Nodup**，矛盾消失。
2. **保持 compose_input 的"依赖传递"物理直觉**：原始等式是"组合的依赖 = 两规则依赖的拼接"——去重拼接保留了这个直觉（重复依赖只算一次），而方案 2A/2B 取单值丢失了两输入的信息。
3. **compose_assoc 仍必需**：dedup 与 ++ 的结合性自然相容（`dedup(x ++ y) = dedup(dedup(x) ++ dedup(y))`），不需要额外假设。
4. **物理对应清晰**：去重拼接对应"规则组合时，重复的依赖关系只记录一次"——这是编译器/依赖图的常规做法，直觉上成立。
5. **对现有体系的冲击最小**：`instNatAdd`（input 为空）和 `instNatLeft`（input 为空）**仍满足新等式**（空列表去重仍是空列表），所以 v23 的独立性定理不会被破坏——只需更新投影函数。

**已知风险**：
- **dedup 是否符合物理直觉？** 如果重复依赖有物理意义（比如某个依赖出现两次意味着双重约束），去重就丢了信息。但目前没有任何物理模型验证这一点，属于未检验假设。
- **旧模型的兼容性**：v11.2.8 Fin 7 模型（input 为空）在新等式下仍成立（空列表拼接去重还是空列表）；但如果要迁移到非空 input 的 Fin 7 模型，需要重新构造 input 函数。
- **编译器实例不变**：`instNatAdd/Left` 仍满足新等式，但它们的 input 本来就是空的，所以 weving 前提在这些实例中**仍空洞**——weaving 的非空性要在有非空 input 的模型里验证（比如 ℕ 上的重复列表模型）。

---

## 任务 4：冻结选项

**"不改"（方案 1）是一个严肃的选项，不是保守退缩**。它有明确的价值主张：

### 冻结选项的价值判断
- **能主张什么**：
  - Core Collapse 是**数学上最硬的结构定理**——它不依赖任何物理诠释，只依赖 `compose_input + input_nodup` 三条公理，就能强制 input ≡ []。这是"信息论压缩原理"的形式化体现：任何包含重复信息的结构（比如 `α∘α` 把相同依赖拼接）都会被 Nodup 约束坍缩到空结构。
  - v23 体系的 474 条定理**全部不依赖坍缩之外的 input 字段**——它们的正确性不受 input 定义的影响。坍缩链条是**独立的装饰**，不是骨架。
  - op_weaving（output 层编织）仍可以有非空洞模型（Fin 7/8），所以"增强体系提供自洽的因果结构"这个主张仍成立，只是要限定在 output 层。
- **不能主张什么**：
  - **不能主张 input 层因果存在**（weaving_axiom 的前提恒假）。
  - **不能主张完整的 A–K 形式化了离散因果**——只能说 output 层形式化了 output 编织，input 层被坍缩证否。
  - **不能声称模型有物理应用**——空洞的公理无法承载物理诠释。
- **物理诠释上的尴尬**：AxiomB/AxiomB' 的 9 个字段花了很大力气形式化，但其中 weaving_axiom 前提恒假——这意味着我们花时间形式化了一个物理上不存在的结构。

**冻结 vs 改的边界条件**：
- 如果你的目标是"让 CSQIT 成为一个自洽的因果+量子框架"——**推荐改（2C）**。
- 如果你的目标是"研究 Core Collapse 本身的数学性质"——**冻结**。
- 如果你的目标是"尽可能少动现有代码"——**冻结**。
- 如果你的目标是"让增强体系的物理意义成立"——**必须改**。

---

## 附录：依赖测绘方法说明

- 依赖测绘范围：v23 主体系 `CSQIT_W1/*.lean`（474 条 theorem/lemma）、增强体系 `CSQIT_Enhanced/*.lean`（Bridge.lean 11 条、Axioms.lean 27 条、EnhancedModels.lean 26 条）、独立测试 `AxiomIndependence.lean`。
- 直接依赖判定：定理陈述或证明中直接引用 `compose_input` / `input_nodup` / `core_collapse` / `input_must_be_empty` 的字段或定理名。
- 间接依赖判定：定理证明中 `rw [core_collapse]`、`exact core_collapse`、或引用直接依赖定理的推论。
- 传递依赖扫描：用 `analysis_axioms.tsv` 的 474 条 `#print axioms` 结果交叉核对，确认坍缩链条封闭在 4 个模块内。
- 覆盖范围：全量（474 + 64 ≈ 538 条），无遗漏。未覆盖：v11.2.0 归档版本（只读，不做改动）。
