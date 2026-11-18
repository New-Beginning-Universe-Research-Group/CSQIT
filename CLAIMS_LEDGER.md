# CLAIMS_LEDGER · 主张边界台账（v23-fix，2026-11-06）

> 工作区：`D:\CSQIT-v23-fix`。
> 范围：只新增本文档；**未修改任何 `.lean` 文件、未修改任何 `.tex` 文件、未 commit 任何代码**。
> 本文档本身可 commit。
> 本文档**不新增数学结论、不替论文补论证、不运行 `lake build`**；验证只引用已有审计产物
> `analysis_axioms.log`、`analysis_axioms.tsv`、`analysis_data.tsv`、`analysis_axioms_enhanced.log`
> 与仓库内 Lean 源文件的定理陈述。
>
> 标记约定：
> - **[事实]**：可直接核对到 Lean 定理、源文件行号或审计日志的陈述。
> - **[推断]**：本文档给出的判断或建议，不是已证定理。
> - **[建议]**：可直接贴进论文的替代表述（一句话），尚未执行。
> - 三张台账表中：**「支撑定理」列 = [事实]**（或明确写「无」）；**「推荐替代表述」列 = [建议/推断]**。
>
> 档位沿用四档：**模型内定理 / 条件定理 / 诠释假设 / 未形式化**。
> 两处例外如实标注：全局性元层事实标为「元层审计（非定理）」，纯计数事实标为「未形式化（可计数）」。

---

## 0. 事实基线（本台账引用的全部事实）

| # | 事实 | 证据 |
|---|---|---|
| F1 | v23 现有 **474** 条 theorem/lemma；分级 **D 28 / C 201 / S 27 / P 218**；`sorryAx = 0` | `analysis_data.tsv`（474 行数据 + 分级列）；`analysis_axioms.log`；本次复核同上 |
| F2 | 全量构建成功：**2229 jobs**，含 32 个 `CSQIT_W1` 构建目标与 4 个 `CSQIT_Enhanced` 命题模块 | 任务简报给定；本次未重跑（避免抢构建锁）。`lakefile.lean` 实有 32 + 5 个 roots（多出的 `AxiomAuditEnhanced` 为纯审计文件，不产定理） |
| F3 | `curvature_energy_strict_decreasing` **为假**：`1 < 8` 但 `ce 1 < ce 8` | `CSQIT_W1/CurvatureEnergyRefutation.lean:71` `curvature_energy_not_strict_decreasing`；`:83` `curvature_energy_counterexample`；零 sorry、零新增 axiom |
| F4 | `compose_input + input_nodup` 与任何非空 `input` 不相容；`weaving_axiom` / `weaving_axiom'` 前提在**任何** A / A′ 模型中恒假 | `CSQIT_Enhanced/Bridge.lean:37` `base_input_empty`；`:59` `base_weaving_vacuous`；`:72` `enhanced_input_empty`；`:97` `enhanced_weaving_vacuous`；审计 `analysis_axioms_enhanced.log:25-30`（仅 `propext`） |
| F5 | 增强版**唯一**非空洞的编织公理是 output 层的 `AxiomD'.op_weaving`；`weaving_axiom'` 本身仍恒假。Fin 7 见证 α=0、β=1、γ=1 | `CSQIT_Enhanced/Bridge.lean:116-135` `fin7_opweaving_premise_witness`、`fin7_opweaving_conclusion_witness`、`fin7_opweaving_nonvacuous` |
| F6 | 决定性格局：Forced = 42、105、420、840、289、8、Ω_Λ 编码值；Free = 12、60、168、64、α⁻¹、250/9（均有 `no_determiner`）；External = H₀（30/61 与经验值） | `DETERMINACY.md` §主表；`IndependenceCheck.lean:200` `no_determiner` 及 :222-414 各实例定理 |
| F7 | `{2,3,5,7}` **不是**满足 `e₁²−e₃=p₁p₂p₄` 的唯一基底：[1,12]⁴ 内 36 解；全局解集无穷；素数类中它只是字典序最小解 | `IndependenceCheck.lean:742` `solsUpTo_12_eq`；`:1126` `prime_solution_lex_min`；`:1182` `primeSolsUpTo_12_eq`；`LAWS.md` D2/D4 |
| F8 | 论文统计过时：称 451 条定理 / 28 模块 /「恰好一个 sorry」/ 9,825 行；实测 474 条 / 29 个命题模块（+4 增强）/ 构建内零 sorry；当前 33 个文件共 **10,158 物理行**（8,403 非空行） | 论文 `paper_revision/csqit_w1_paper.tex:533-540`、`:613-623`；`csqit_w1_paper_zh.tex:368`、`:434`；审计 `analysis_data.tsv`；本次 `(Get-Content).Count` 求和 |
| F9 | `GenerationBridge.lean` 现为 **65 行墓碑**，含 4 条纯数论定理，参与构建；原 1948 行原文退役为 `GenerationBridge_legacy.lean.disabled`（唯一真 sorry 在旧 :1427，不在构建内） | `CSQIT_W1/GenerationBridge.lean:1-65`（`A4_order_decompose`、`A5_order_decompose`、`PSL27_order_decompose`、`hurwitz_orders_eq_base_subset`）；`BOUNDARIES.md` §8 |
| F10 | `Declaration.lean` 为 **137 行 / 13 条定理**（与论文一致；`Get-Content .Count` 物理行计数） | 本次 `(Get-Content).Count` + `^(theorem|lemma) ` 计数；`CSQIT_W1/Declaration.lean:119` |
| F11 | `CSQIT_W1` 共 33 个 `.lean` 文件、32 个 lake roots（`AxiomAuditAll.lean` 不在 roots）；其中**有定理的模块 29 个**。`CSQIT_Enhanced` 共 5 个 `.lean`、5 个 roots，其中有定理的模块 4 个 | `lakefile.lean:23-56`、`:62-68`；本次逐文件定理计数（`TheoryFoundations` / `AxiomAudit` / `AxiomAuditAll` / `SolsAnyFamilies` 零定理） |
| F12 | 构建模块内文本 "sorry" 共 **22 处，全为注释**；另 1 处在退役文件中（旧 :1427） | 本次 `Select-String 'sorry'` + `analysis_axioms.log` 零 `sorryAx` |
| F13 | 全库**无 Lean `axiom` 声明**；假设以 `class` / `def` 字段与定理参数形式出现 | `Select-String '^axiom '` 在 `CSQIT_W1/*.lean` 零命中；`AxiomAudit.lean` 审计集仅 `propext / Classical.choice / Quot.sound`；`BOUNDARIES.md` 头部 |
| F14 | **474 条 theorem/lemma 全部带紧邻 W1/W2/W3 层级标签（474/474）**；本轮新增 291 行标签注释（274 条首次标注 + 17 条重复标注），新增分布 W1 209 / W2 43 / W3 39；全库最终分布 W1 379 / W2 55 / W3 40 | `paper_revision/tier_label_audit_474.md`（定稿，逐文件表）；`git diff --ignore-cr-at-eol --numstat b1e1e25..HEAD`（22 文件、+295/−0）；`audit_tiers.py` 机器复核 `TOTAL_DECL=474 / MISSING=0` |

---

## 1. 台账 A · 可主张（有定理支撑）

> 判定标准：主张的**字面内容**与 Lean 定理陈述一致。允许附一句适用范围（如「在 CompilerAxiom 模型内」），
> 但不得把模型内结论改写成物理结论。

| # | 主张原句（出处） | 支撑定理（Lean 名） | 当前档位 | 推荐替代表述 [建议] |
|---|---|---|---|---|
| K1 | "Core Collapse: for every α : C, input α = []"（EN `:292-299`；ZH `:170-176`） | `CSQIT_W1.CompilerAxioms.core_collapse`；`CSQIT_W1.CoreCollapse.no_causal_input` | 模型内定理 | 保留原句；建议补一句「在 `CompilerAxiom` 五字段模型内无条件成立（`core_collapse`）」。 |
| K2 | "Core Collapse 在增强体系中同样成立"（内部表述；`BRIDGE_COMPILER.md` §6） | `CSQIT_Enhanced.base_input_empty`；`CSQIT_Enhanced.enhanced_input_empty`（仅依赖 `propext`） | 模型内定理 | 「`AxiomA` 与 `AxiomA'` 同样强制 `input ≡ []`（`base_input_empty` / `enhanced_input_empty`），标准版与增强版在 input 层同构。」 |
| K3 | "Associativity is redundant; minimal axiom system for Core Collapse is A1–A3"（EN `:342-348`；ZH `:205-211`） | `CSQIT_W1.AxiomIndependence.minimal_core_collapse`（`MinimalCompilerAxiom` 无 `assoc` 字段） | 模型内定理 | 「Core Collapse 的证明只消费 `compose_input` 与 `input_nodup`；`assoc` 冗余（`minimal_core_collapse`）。」 |
| K4 | "No rule has any dependency: x ∉ input α"（EN `:325-329`；ZH `:195-198`） | `CSQIT_W1.CoreCollapse.no_causal_input`；`CSQIT_W1.CompilerAxioms.no_dependency` | 模型内定理 | 保留原句，标明它是 `core_collapse` 的直接推论。 |
| K5 | "Finite-Free Two-Aspect Dichotomy ... No finiteness assumption on C"（EN `:426-435`；ZH `:262-270`） | `CSQIT_W1.TwoAspectNoFinite.two_aspect_dichotomy_no_finite` | 模型内定理 | 保留原句；建议注明前提为 `AxiomA` + `AxiomC` 实例。 |
| K6 | "e₁²−e₃ = 17²−247 = 42 = p₁p₂p₄"（EN `:732-744`；ZH `:489-503`） | `CSQIT_W1.QuantumCorrection.e1_sq_sub_e3_eq_p1p2p4`；唯一性 `IndependenceCheck.forty_two_unique_of_base` | 模型内定理（基底给定） | 「在基底 `{2,3,5,7}` 上，`e₁²−e₃ = 42 = p₁p₂p₄`；这是从 `e₁/e₃` 定义经 `norm_num` 得到的算术恒等式。」 |
| K7 | "n = N/4 = 105; cos(2π·105/420) = 0"（EN `:753-761`；ZH `:507-516`） | `CSQIT_W1.ObserverLayering.alpha_level_n_eq_105`；`cos_at_alpha_level`；`observed_equals_bare_at_alpha_level` | 模型内定理（基底给定） | 「`105 = p₂p₃p₄`；在 `N = 420` 下 `cos(2π·105/420)=0`（`alpha_level_n_eq_105`、`cos_at_alpha_level`）。」 |
| K8 | "Ω_Λ = S²/420 = 289/420"（EN `:849-851`；ZH `:584-586`） | `CSQIT_W1.PhysicalConnect.omega_Lambda_eq_darkEnergyNum_ratio`；`Foundation.darkEnergyNum_eq_289` | 模型内定理（编码值） | 「编码值 `Ω_Λ := 289/420`（`omega_Lambda_eq_darkEnergyNum_ratio`）；该分数是否等于观测暗能量密度是另一问题（见 C6）。」 |
| K9 | "two encodings proven algebraically identical"（EN `:209-219`；ZH `:97-98`） | `WeaverPopulation.alpha_inv_exact_eq_inverseFineStructure`（`rfl`）；`Declaration.declaration_alpha_inv_consistency` | 模型内定理 | 「`Foundation.inverseAlpha` 与 `MinimalCost.alpha_inv mkBase` 是同一闭式的两种编码，`declaration_alpha_inv_consistency` 证明二者相等；这是编码一致性，不是两条独立推导。」 |
| K10 | "zero axioms"（外部/内部表述，非当前论文原句） | 无（元层审计：`analysis_axioms.log` 全库零 `sorryAx`、仅标准三公理；`^axiom ` 零命中） | 元层审计（非定理） | 「无 Lean `axiom` 声明；假设以 `class` / `def` 字段与定理参数形式存在；审计依赖仅 `propext`、`Classical.choice`、`Quot.sound`。」 |
| K11 | "MUST_HAVE = {2,3,5,7}"（EN `:486-488`；ZH `:324-326`） | `CSQIT_W1.SequenceStructure.MUST_HAVE_eq_base`；`union_of_prime_factors_eq_base` | 条件定理（群阶给定） | 「三个**宣言**群阶 12、60、168 的素因子并集恰为 `{2,3,5,7}`（`MUST_HAVE_eq_base`）。」 |
| K12 | "宇宙不可无限分解"（DETERMINACY 假设 7 的形式版） | `IndependenceCheck.no_infinite_decomposition`；`prime_factorization_unique`；`exists_prime_factor_ge2` | 模型内定理（ℕ 模型） | 「在 ℕ 分解结构模型内，不存在无穷真因子分解链（`no_infinite_decomposition`）；物理宇宙版本是诠释假设。」 |
| K13 | "Every theorem carries an explicit tier label"（EN 摘要 `:41-42`；ZH 摘要 `:37`）；"Every theorem statement specifies its tier"（EN `:185`；ZH `:87`） | **474/474 条 theorem/lemma 均带紧邻层级标签**（`tier_label_audit_474.md` 逐文件表；`audit_tiers.py` 复核 `MISSING=0`；判定口径 `TIER_CRITERIA.md`） | 元层审计（非定理，可计数） | 保留原句；如需脚注可写「474 条 theorem/lemma 全部带紧邻标签，逐文件分布见 `paper_revision/tier_label_audit_474.md`」。 |

**小计：13 条。**

---

## 2. 台账 B · 只能条件主张（须带前提）

> 判定标准：定理为真，但结论只在明确前提（基底 / 群阶 / 规则 / 经验输入）下成立。
> 论文若省略前提，即从 B 栏滑入 C 栏。

| # | 主张原句（出处） | 支撑定理（Lean 名） | 当前档位 | 推荐替代表述 [建议] |
|---|---|---|---|---|
| C1 | "Unique Basis ... if B is any set of primes with MUST_HAVE ⊆ B ⊆ MUST_HAVE, then B = MUST_HAVE"（EN `:486-492`；ZH `:324-330`） | `SequenceStructure.base_uniqueness_by_exclusion`；`unique_base_is_2357`（前提 `h1 : MUST_HAVE ⊆ B`、`h2 : B ⊆ MUST_HAVE`） | 条件定理 | 「给定三个声明群阶，且基底既覆盖全部必须素因子又无冗余时，基底等于 `{2,3,5,7}`（`unique_base_is_2357`）；第二条包含关系本身就是「无冗余」前提，不构成全局唯一性。」 |
| C2 | "closure sequence ... 420 = lcm(12,60,168)/2"（EN `:52-53`、`:740-743`；ZH `:39`、`:503`） | `Foundation.totalClosure_eq_420`（`simp` + `decide`）；`IndependenceCheck.totalClosure_unique_of_orders`（前提群阶 12/60/168） | 条件定理 | 「在宣言群阶 (12,60,168) 与 `lcm/2` 规则下，闭包值为 420（`totalClosure_eq_420`）；群阶与 `/2` 规则均为定义选择。」 |
| C3 | "closure sequence C = {8, 64, 420, ...} whose values are fixed by declared rules"（EN `:51-53`；ZH `:39`） | `Foundation.closure_sequence_extended`（8/64/420/840 字面模式，`Foundation.lean:565`）；`level64_not_determined_by_fields` | 条件定理 + 定义选择 | 「闭包序列的前几项由 `closure_sequence_extended` 的规定写入：8 与 64 是字面项，420 由 `lcm(12,60,168)/2` 算出；序列不是从五字段公理推导出来的。」 |
| C4 | "α⁻¹ = 137.036 ... closed form is a declared definition choice"（EN `:48-50`；ZH `:39`） | `Foundation.inverseAlpha_eq_137_036`；`MinimalCost.WeavingBase.alpha_inv_mkBase_eq_137p036`；`IndependenceCheck.alpha_inv_not_determined_by_fields` | 条件定理（基底 + 公式选择） | 「在基底 `{2,3,5,7}` 与公式 `p₁^p₄ + p₁^p₂ + 1 + p₂²/(p₁p₃³)` 被给定后，α⁻¹ = 137+9/250（`inverseAlpha_eq_137_036`）；公式与基底均为定义选择。」 |
| C5 | "attractor uniqueness given this form"（EN `:841-843`；ZH `:577-578`） | `AttractorPrototype.attractor_unique`；`Declaration.declaration_attractor_unique` | 条件定理 | 「在公式形式与递增素数约束下，`(2,3,5,7)` 是唯一锁定解（`attractor_unique`）；形式本身不是 CSQIT 推论。」 |
| C6 | "Ω_Λ ≈ 0.688 ... dark energy density"（隐含于 Ω 系列；EN `:849-851`；ZH `:584-586`） | 无对应物理定理；只有编码恒等式 `PhysicalConnect.omega_Lambda_eq_darkEnergyNum_ratio`；Planck 经验值未进入任何定理结论 | 诠释假设 / External | 「`289/420 ≈ 0.688` 是框架编码值；与 Planck 2018 观测值的对应是经验比较，未形式化。」 |
| C7 | "H₀ = α⁻¹·30/61 ≈ 67.4"（内部表述；`BOUNDARIES.md` §1） | `Foundation.hubbleConstant_eq`；`IndependenceCheck.hubble_not_determined_by_fields`；`Foundation` 中 `30/61` 字面定义 | 条件定理 + External | 「`H₀ := α⁻¹·30/61` 是定义选择（`hubbleConstant_eq`）；`30/61` 不在基底 P 中，其取值以匹配经验 H₀ 为目标（`hubble_not_determined_by_fields`）。」 |
| C8 | "Canonical minimal basis {60,168}"（`LAWS.md` C3；论文未直接陈述） | `IndependenceCheck.canonicalClosure_minimal_basis`（含 drop12/drop60/drop168 判定；前提：闭包系统 + 正性） | 条件定理 | 「在声明闭包系统中，`{60,168}` 是 420 的最小子基：去掉 12 值不变，去掉 60 或 168 值变（`canonicalClosure_minimal_basis`）。」 |
| C9 | "Ω-和 = 1"（`LAWS.md` D6；论文未直接陈述） | `IndependenceCheck.altOmegaSum_eq_one_iff`（前提：分子固定为 20、111、289）；反例 `omega_sum_one_with_N_ne_420` | 条件定理 | 「在分子固定为 (20,111,289) 时，`Ω`-和 = 1 与闭包值 = 420 等价（`altOmegaSum_eq_one_iff`）；单独的「和为 1」不刻画 420（`omega_sum_one_with_N_ne_420`）。」 |
| C10 | "Any theory whose symmetry group is among these three groups must use the prime basis {2,3,5,7}"（EN `:724-730`；ZH `:480-487`） | `SequenceStructure.MUST_HAVE_eq_base`；`removing_2/3/5/7_breaks_*` | 条件定理 + 诠释假设 | 「若一个理论的对称群恰为 `A₄/A₅/PSL(2,7)` 之一，则其素因子并集为 `{2,3,5,7}`；「理论必须使用该基底」是建模选择，不是定理。」 |
| C11 | "All other results ... are W1 strict derivations from these five choices"（EN `:860-864`；ZH `:594-597`） | 多数结果有定理：`core_collapse`、`e1_sq_sub_e3_eq_p1p2p4`、`alpha_level_n_eq_105`、`totalClosure_eq_420`；但 8/64 为字面项，两个必要性反例未形式化 | 条件定理（部分条目为定义展开） | 「其余结果是从五个宣言选择出发的 W1 推导；其中闭包序列的 8 与 64 是定义的字面项，420 是 lcm 计算；次可加性与去 Nodup 的反例是论文层面的论证（尚未 Lean 形式化）。」 |

**小计：11 条。**

---

## 3. 台账 C · 不可主张（已被证否或无支撑）

> 判定标准：按字面核查会被 Lean 定理或审计日志直接否定，或代码库中不存在可指认的定理。
> 「无」表示**没有任何 Lean 定理**支撑该句。

| # | 主张原句（出处） | 支撑定理 / 证否证据 | 当前档位 | 推荐替代表述 [建议] |
|---|---|---|---|---|
| N1 | "a unique prime basis {2,3,5,7}"（EN `:48`、`:141-143`；ZH `:39`、`:68`；section 标题 `:297`） | **证否**：`prime_solution_lex_min`（只是素数类**字典序最小**，不是唯一）；`solsUpTo_12_eq`（[1,12]⁴ 内 36 解）；`vieta_partner`（全局解集无穷）；`no_determiner` 表明基底不被五字段公理决定 | 未形式化（唯一性无支撑） | 「the declared prime basis `{2,3,5,7}`; it is the lexicographically least prime solution of `e₁²−e₃=p₁p₂p₄`, not the unique one.」（中文：宣言素基底 `{2,3,5,7}`；它是该恒等式在素数基底类中的字典序最小解，不是唯一解。） |
| N2 | "CSQIT derives 420 / the closure sequence from the axioms"（历史/对外表述；`README.md` 系列；论文摘要的 "derives at the W1 level" 为其弱化版） | **证否**：`closure_not_determined_by_fields`、`order12/60/168_not_determined_by_fields`（五字段无决定函数）；`totalClosure` 是 `Nat.lcm (Nat.lcm 12 60) 168 / 2`（`Foundation.lean:114`）；`closure_sequence_extended` 是字面 match（`:565`） | 未形式化（「由公理推出」已被证否） | 「420 is computed from the declared group orders and the declared `lcm/2` rule; the causal axioms do not determine it (`closure_not_determined_by_fields`).」（中文：420 由宣言群阶与 `lcm/2` 规则算出；因果公理不决定它。） |
| N3 | "a coupling constant with two independent derivations converging on the same value"（cover letter `cover_letter.txt:62-63`；历史表述） | **证否**：`alpha_inv_exact_eq_inverseFineStructure` 为 `rfl`（定义性相等）；`declaration_alpha_inv_consistency` 把两边同时改写为 `137 + 9/250`（同一闭式的两种编码）；`alpha_inv_not_determined_by_fields` | 未形式化（「独立推导」无支撑） | 「two encodings of the same declared closed form, proved identical (`declaration_alpha_inv_consistency`); this is not two independent derivations.」（中文：同一宣言闭式的两种编码，已证相等；这不是两条独立推导。） |
| N4 | "A–J（或 A–K）formalize discrete causality"（内部表述：`BRIDGE_COMPILER.md:10` 的覆盖表；`DESIGN_OPTIONS.md:208` 明确划界） | **证否**：`base_input_empty`、`enhanced_input_empty` 强制 `input ≡ []`；`base_weaving_vacuous`、`enhanced_weaving_vacuous` 使 `weaving_axiom`/`weaving_axiom'` 前提恒假；`CompilerAxiom` 无 `M → M → Prop` 字段（`BRIDGE_COMPILER.md` §4）；仅 `fin7_opweaving_nonvacuous`（output 层）非空洞 | 未形式化（input 层因果已被证否） | 「The enhanced system formalizes output-layer weaving (`AxiomD'.op_weaving`, with a Fin 7 witness); its input-layer causality axioms (`weaving_axiom`/`weaving_axiom'`) are vacuous in every model, so discrete causal order is not expressible in the present axiom system.」（中文：增强体系只形式化了 output 层编织；input 层因果序前提恒假，现有公理体系无法表达离散因果序。） |
| N5 | "GenerationBridge compiles without errors"（历史/对外表述；v17–v23 期间） | **证否**：原 1948 行模块从未编译通过，唯一真 sorry 在旧 `:1427`；现 `GenerationBridge.lean` 为 65 行墓碑（4 条纯数论定理）才进入构建（`BOUNDARIES.md` §8） | 未形式化（原模块已退役） | 「The legacy 1,948-line module never compiled; it is retired to `GenerationBridge_legacy.lean.disabled`. The current 65-line tombstone contains four pure number-theory theorems and compiles as part of the build.」（中文：原 1948 行模块从未编译通过，已退役；现 65 行墓碑含 4 条纯数论定理并参与构建。） |
| N6 | "curvature_energy is strictly decreasing"（v12/GB 历史表述；现 `GenerationBridge.lean` 头已自证否） | **证否**：`curvature_energy_not_strict_decreasing`；`curvature_energy_counterexample`（`a=1 < b=8` 但 `ce 1 < ce 8`） | 未形式化（全定义域命题为假） | 「`curvature_energy` is not strictly decreasing on its whole domain; a formal counterexample is `curvature_energy_counterexample`. Any 'n ≥ 8 decreasing' statement is an analytical claim, not yet formalized.」（中文：全定义域严格递减为假（已形式化反例）；「n ≥ 8 递减」仅为分析性论证，尚未形式化。） |
| N7 | "All results are formalized in Lean 4 with Mathlib"（EN `:531-532`；ZH `:365-368`） | **无**：`AxiomIndependence.lean` 只有 1 条定理 `minimal_core_collapse`；论文 §5.2「次可加失败」与 §5.3「去 Nodup 失败」的反例只存在于注释（`AxiomIndependence.lean:83-149`），无对应定理名 | 未形式化 | 「All numbered theorems except the two counterexample arguments in §§5.2–5.3 are formalized in Lean; the associativity-redundancy claim is formalized (`minimal_core_collapse`), while the two necessity counterexamples remain paper-level arguments.」（中文：除 §5.2–§5.3 两个反例论证外，所有编号定理均已形式化；结合律冗余已由 `minimal_core_collapse` 形式化。） |
| N8 | "28 Lean modules, 9,825 lines, 451 theorem/lemma/corollary declarations, 129 definitions ... exactly one sorry"（EN `:533-540`、`:613-623`；ZH `:368`、`:434`；cover letter `:97`） | **计数不符**：474 条（`analysis_data.tsv`）；29 个命题模块 + 4 增强（F11）；构建内零 sorry（F1/F12）；当前 33 文件共 10,158 物理行（F8）；构建模块 22 处 "sorry" 全为注释（F12） | 未形式化（可计数事实） | 「474 theorem/lemma declarations across 29 theorem-bearing modules (33 `.lean` files; 32 build roots), plus 4 theorem-bearing enhanced modules; the full build has zero `sorry` and zero `sorryAx`, and no Lean `axiom` declaration.」（中文：29 个命题模块共 474 条定理（33 个 `.lean` 文件、32 个构建根），另有 4 个增强命题模块；全量构建零 sorry、零 sorryAx，且无 Lean axiom 声明。） |
| N9 | "GenerationBridge ... has not been fixed, and the module currently does not compile"（EN `:598-607`；ZH `:422-428`） | **证否（就现仓库而言）**：现 `GenerationBridge.lean` 65 行、4 条定理、参与构建；全量构建 0 错误（F2/F9）。原文的「未修复」已不成立；只是「原文退役」而非「带错留在构建里」 | 未形式化（当前陈述已过时） | 「The legacy module was not fixed but retired: its content is disabled and the current tombstone compiles.」（中文：原文未被「修复」而是被「退役」；现墓碑模块编译通过。） |
| N10 | "the five definition choices are exactly the external dependencies of the W1 core"（EN `:875-885` 未来工作；ZH `:602-603`） | **无**：`DETERMINACY.md` 显示 H₀ 为 External（30/61 框架外字面 + 经验值），CODATA 137.035999206 以定理前提出现（`ObserverLayering.lean:187-189`）；因此外部依赖不止五个选择 | 未形式化 | 「The five choices are the declared mathematical starting points; the W1 core additionally uses external empirical values only as theorem hypotheses (e.g. CODATA in `ObserverLayering.lean`), which an automated checker must track separately.」（中文：五个选择是宣言的数学起点；W1 核心另有以定理前提形式出现的外部经验值（如 CODATA），自动检查器需单独追踪。） |

**小计：10 条。**

**合计：34 条（可主张 13 / 条件主张 11 / 不可主张 10）。**

---

## 4. 论文待同步清单（只列，不执行）

> 目标文件：`paper_revision/` 下的两份 tex 与一份 cover letter。
> 每条格式：**文件:行号 → 现文 → 建议新文**。
> 行号按 2026-11-06 的文件状态；若已重排，以引文定位为准。

### 4.1 `paper_revision/csqit_w1_paper.tex`（12 条）

| # | 行号 | 现文（摘录） | 建议新文 |
|---|---|---|---|
| EN-1 | `:48` | "derives at the W1 level: a unique prime basis $\{2,3,5,7\}$" | "proves at the W1 level that the union of prime factors of the three declared group orders is $\{2,3,5,7\}$; this basis is the lexicographically least prime solution of $e_1^2-e_3=p_1p_2p_4$, not the unique one" |
| EN-2 | `:51-53` | "a closure sequence $\mathcal{C} = \{8, 64, 420, \ldots\}$ whose values are fixed by declared rules" | "a closure sequence $\mathcal{C} = \{8, 64, 420, \ldots\}$ whose entries are given by a declared definition: 8 and 64 literally, 420 as $\mathrm{lcm}(12,60,168)/2$" |
| EN-3 | `:141-143` | "unique prime basis" | "declared prime basis $\{2,3,5,7\}$ (identified as the union of the prime factors of the three declared group orders)" |
| EN-4 | `:486-492` | "\begin{theorem}[Unique Basis, W1] ... if $B$ is any set of primes with MUST_HAVE ⊆ B ⊆ MUST_HAVE, then B = MUST_HAVE." | 标题改为 `[Basis Determination, W1]`；正文改为 "$\mathrm{MUST\_HAVE}=\{2,3,5,7\}$. Moreover, any prime set $B$ that contains $\mathrm{MUST\_HAVE}$ and contains no redundant primes (i.e. $B\subseteq\mathrm{MUST\_HAVE}$) equals $\mathrm{MUST\_HAVE}$. This uniqueness is relative to the declared group orders; it is not uniqueness among all prime bases." |
| EN-5 | `:525-526` | "the uniqueness is proved by \texttt{unique\_base\_is\_2357}" | "the relative uniqueness is proved by `unique_base_is_2357`; global uniqueness among prime bases is not claimed (see `prime_solution_lex_min`: lexicographic least, and `solsUpTo_12_eq`: 36 solutions in $[1,12]^4$)" |
| EN-6 | `:531-532` | "All results are formalized in Lean~4 with Mathlib." | "All numbered theorems except the two counterexample arguments in §§5.2–5.3 are formalized in Lean~4 with Mathlib; those two remain paper-level arguments." |
| EN-7 | `:533-540` | "28 Lean modules totaling 9,825 lines: 451 ... 129 ... exactly one \texttt{sorry}" | "29 theorem-bearing modules (33 `.lean` files, 32 build roots) totaling 10,158 physical lines (8,403 non-blank): 474 theorem/lemma declarations and 153 definition/structure/inductive declarations. The full build contains zero `sorry` and zero `sorryAx`; no Lean `axiom` declaration occurs in the repository." |
| EN-8 | `:577` | "Concentrated declaration (added in this session)." | "Concentrated declaration (added in the consolidated release)." |
| EN-9 | `:587-596` | "compiles with \emph{zero errors}, producing a 33 KB \texttt{.olean}" | "compiles with zero errors"（删除易变的 `.olean` 体积；137 行/13 条定理的计数本身正确，无需改） |
| EN-10 | `:598-607` | "GenerationBridge.lean's two earlier compilation bugs ... have not been fixed, and the module currently does not compile; its single W2-conditional sorry therefore remains outside the declaration chain." | "The legacy \texttt{GenerationBridge.lean} (1,948 lines) never compiled; it is retired to \texttt{GenerationBridge\_legacy.lean.disabled} (excluded from the build). The current \texttt{GenerationBridge.lean} is a 65-line tombstone containing four pure number-theory theorems, which compiles as part of the full build. The historical \texttt{sorry} (legacy line 1427) is outside the build; the build contains zero \texttt{sorry}." |
| EN-11 | `:613-623` | "28 Lean modules totaling 9,825 lines: 451 ... exactly one \texttt{sorry} ... A naive text search reports 16 occurrences ... the other 15 are comments" | "29 theorem-bearing modules (33 `.lean` files, 32 build roots) totaling 10,158 physical lines (8,403 non-blank): 474 theorem/lemma declarations. The full build contains zero \texttt{sorry}. A naive text search over the 33 files reports 22 occurrences of the word `sorry`, all in comments; the one real `sorry` (legacy line 1427) lies in the disabled file and outside the build." |
| EN-12 | `:860-864` | "All other results in this paper---Core Collapse, minimality, the prime basis $\{2,3,5,7\}$, coupling constant $\alpha^{-1} = 137.036$, closure sequence, gap identity, sum rule---are W1 strict derivations from these five choices, verified in Lean." | "All other results in this paper---Core Collapse, minimality, the prime-basis identification, the declared $\alpha^{-1}=137.036$, the $420=\mathrm{lcm}(12,60,168)/2$ computation, the gap identity, and the sum rule---are W1 derivations from these five choices, verified in Lean. Qualification: entries 8 and 64 of the closure sequence are literal entries of a declared definition, and the two necessity counterexamples in §§5.2–5.3 are not yet formalized." |

### 4.2 `paper_revision/csqit_w1_paper_zh.tex`（12 条，与 EN 逐条对应）

| # | 行号 | 现文（摘录） | 建议新文 |
|---|---|---|---|
| ZH-1 | `:39` | "唯一素基底（unique prime basis）$\{2,3,5,7\}$" | "三个宣言群阶的素因子并集为 $\{2,3,5,7\}$；该基底是 $e_1^2-e_3=p_1p_2p_4$ 在素数基底类中的字典序最小解，不是唯一解" |
| ZH-2 | `:39` | "closure 序列 ...（其数值由宣言在案的规则固定）" | "closure 序列 ...（其项由宣言定义给出：8 与 64 为字面项，420 为 $\mathrm{lcm}(12,60,168)/2$ 的计算值）" |
| ZH-3 | `:68` | "唯一素基底" | "宣言素基底 $\{2,3,5,7\}$（由三个宣言群阶的素因子并集确定）" |
| ZH-4 | `:297` | "\section{序列结构与唯一基底}" | "\section{序列结构与基底识别}" |
| ZH-5 | `:324-330` | "\begin{theorem}[唯一基底，W1] ... 若 $B$ 是任意素数集合，满足 MUST_HAVE ⊆ B ⊆ MUST_HAVE，则 B = MUST_HAVE." | 标题改为 `[基底识别，W1]`；正文改为 "$\mathrm{MUST\_HAVE}=\{2,3,5,7\}$。此外，若素数集合 $B$ 覆盖 $\mathrm{MUST\_HAVE}$ 且不含冗余素因子（即 $B\subseteq\mathrm{MUST\_HAVE}$），则 $B=\mathrm{MUST\_HAVE}$。该唯一性是相对于宣言群阶而言，不是素数基底类中的全局唯一性。" |
| ZH-6 | `:361-362` | "唯一性由 \texttt{unique\_base\_is\_2357} 证明" | "相对唯一性由 `unique_base_is_2357` 证明；不主张素数基底类中的全局唯一性（见 `prime_solution_lex_min`：字典序最小；`solsUpTo_12_eq`：[1,12]⁴ 内 36 解）" |
| ZH-7 | `:368` | "28 个 Lean 模块，共计 9,825 行：451 条 ... 129 条 ... 全项目恰好含有一个 \texttt{sorry}" | "29 个命题模块（33 个 `.lean` 文件、32 个构建根），共 10,158 物理行（8,403 非空行）：474 条 theorem/lemma 声明与 153 条 definition/structure/inductive 声明。全量构建零 \texttt{sorry}、零 \texttt{sorryAx}；仓库无 Lean \texttt{axiom} 声明。" |
| ZH-8 | `:402` | "集中宣言（本次会话新增）" | "集中宣言（随整合版本新增）" |
| ZH-9 | `:412-420` | "以\emph{零错误}编译，生成 33 KB 的 \texttt{.olean}" | "以零错误编译"（删除易变的 `.olean` 体积；137 行/13 条定理的计数本身正确，无需改） |
| ZH-10 | `:422-428` | "\texttt{GenerationBridge.lean} 早先的两个编译缺陷 ... 尚未修复，该模块目前无法编译；其全项目唯一的 \texttt{W2 conditional} \texttt{sorry} 因此留在宣言链之外。" | "原 \texttt{GenerationBridge.lean}（1,948 行）从未编译通过，已退役为 \texttt{GenerationBridge\_legacy.lean.disabled}（不参与构建）。现行 \texttt{GenerationBridge.lean} 是 65 行墓碑，含 4 条纯数论定理，随全量构建编译通过。历史 \texttt{sorry}（旧第 1427 行）在构建之外；构建内零 \texttt{sorry}。" |
| ZH-11 | `:434` | "28 个 Lean 模块 ... 451 条 ... 全项目恰好含有一个 \texttt{sorry} ... 16 处 ... 其余 15 处是注释" | "29 个命题模块（33 个 `.lean` 文件、32 个构建根），共 10,158 物理行（8,403 非空行）：474 条 theorem/lemma 声明。全量构建零 \texttt{sorry}。对 33 个文件做朴素文本搜索会命中 22 处 "sorry"，全部位于注释；唯一的真 \texttt{sorry}（旧第 1427 行）在禁用文件中，位于构建之外。" |
| ZH-12 | `:594-597` | "本文所有其他结果——核心坍缩、极小性、素基底 $\{2,3,5,7\}$、耦合常数 $\alpha^{-1} = 137.036$、closure 序列、缺口恒等式、求和规则——都是从这五个选择出发的 W1 严格推导，并已在 Lean 中验证。" | "本文所有其他结果——核心坍缩、极小性、基底识别、宣言的 $\alpha^{-1}=137.036$、$420=\mathrm{lcm}(12,60,168)/2$ 的计算、缺口恒等式、求和规则——都是从这五个选择出发的 W1 推导，并已在 Lean 中验证。限定：closure 序列中的 8 与 64 是宣言定义的字面项；§5.2–§5.3 的两个必要性反例尚未形式化。" |

> 说明：ZH-1 与 EN-1、ZH-2 与 EN-2、ZH-4 与 EN-4 是同一主张的中英双份，**必须成对修改**，否则两稿会分叉。

### 4.3 `paper_revision/cover_letter.txt`（2 条）

| # | 行号 | 现文（摘录） | 建议新文 |
|---|---|---|---|
| CL-1 | `:61-63` | "derives at the W1 level: a unique prime basis, a coupling constant with two independent derivations converging on the same value, a closure sequence, and nine other theorems" | "proves at the W1 level: that the declared prime basis is the lexicographically least prime solution of the gap identity (not the unique one), that two encodings of one declared closed form for the coupling constant are identical, the $420$ computation from the declared closure rule, and nine other theorems" |
| CL-2 | `:97` | "28 Lean modules, 9,825 lines, 451 theorem/lemma/corollary declarations, 129 definitions; ... exactly one sorry (explicitly marked W2-conditional)" | "29 theorem-bearing modules (33 `.lean` files, 32 build roots), 10,158 physical lines (8,403 non-blank), 474 theorem/lemma declarations, 153 definition/structure/inductive declarations; the full build contains zero `sorry` and zero `sorryAx`, and the repository contains no Lean `axiom` declaration" |

（`Declaration.lean: 13 theorems, 137 lines` 一项与实测一致，无需修改，故删去原 CL-3。）

**待同步条目合计：26 条（EN 12 / ZH 12 / cover letter 2）。**

---

## 5. 对外表述风险（按严重度排序）

> 严重度定义：
> - **P0**：按字面核查会被事实直接打脸（定理、计数器、构建状态任一即可推翻）。
> - **P1**：事实大体成立，但缺乏 Lean 支撑或前提缺失，同行追问一句即失守。
> - **P2**：措辞过强、易被误读，但可辩护。

### P0（8 条）

| # | 原句 | 出处 | 核查会命中的事实 |
|---|---|---|---|
| P0-1 | "a unique prime basis $\{2,3,5,7\}$" | EN `:48`、`:141-143`；ZH `:39`、`:68` | `prime_solution_lex_min` 只证字典序最小；`solsUpTo_12_eq` 在 [1,12]⁴ 内就有 36 解；`vieta_partner` 给出无穷解链 |
| P0-2 | "CSQIT derives 420 / the closure sequence from the axioms"（历史/摘要弱化版） | `README.md` 系列；EN `:48` 的 "derives at the W1 level" | `closure_not_determined_by_fields` + 群阶 no_determiner；`totalClosure` 是字面 `lcm/2` 定义 |
| P0-3 | "a coupling constant with two independent derivations converging on the same value" | cover letter `:62-63`（正文 `:209-216` 已改为「同一闭式两种编码」） | `alpha_inv_exact_eq_inverseFineStructure` 为 `rfl`；`declaration_alpha_inv_consistency` 是同一闭式两种编码 |
| P0-4 | "A–J（A–K）formalize discrete causality" | `BRIDGE_COMPILER.md:10`；`DESIGN_OPTIONS.md:208` 已自我否定 | `base_input_empty`/`enhanced_input_empty` 强制 `input ≡ []`；`base_weaving_vacuous`/`enhanced_weaving_vacuous` 使前提恒假 |
| P0-5 | "GenerationBridge compiles without errors"（旧表述） | v17–v23 历史表述 | 原 1948 行从未编译通过，真 sorry 在旧 `:1427` |
| P0-6 | "curvature_energy is strictly decreasing" | v12/GB 历史表述 | `curvature_energy_not_strict_decreasing` + `curvature_energy_counterexample` |
| P0-7 | "451 theorem/lemma/corollary declarations, 28 modules, exactly one sorry" | EN `:533-540`、`:613-623`；ZH `:368`、`:434`；cover letter `:97` | 实测 474 / 29（+4）/ 构建内零 sorry；9,825 行与当前 10,158 行不符（`Declaration.lean` 137 行本身与论文一致） |
| P0-8 | "All results are formalized in Lean 4 with Mathlib" | EN `:531-532`；ZH `:365-368` | §5.2/§5.3 两个必要性反例在 `AxiomIndependence.lean` 中只是注释，无定理名 |

> 补充说明（不计入 P0 计数）：EN `:598-607` / ZH `:422-428` 的「GB currently does not compile」与 P0-5 方向相反，
> 但对**现仓库**同样为假（现墓碑参与构建，0 错误）。它已列入 N9 与同步项 EN-10/ZH-10。

### P1（4 条）

| # | 原句 | 出处 | 问题 |
|---|---|---|---|
| P1-1 | "zero axioms"（无限定） | 内部/对外摘要 | 事实是「无 Lean `axiom` 声明」；`class` 字段与定理参数仍是假设。限定后可主张（K10），无限定则易被读成「无任何假设」 |
| P1-2 | "closure sequence ... W1 strict derivations" | EN `:860-864`；ZH `:594-597` | 8 与 64 是字面定义项，不是推导值；420 是 lcm 计算 |
| P1-3 | "the five definition choices are exactly the external dependencies of the W1 core" | EN `:875-885`；ZH `:602-603` | H₀ 的 30/61 与 CODATA 137.035999206 是框架外输入；不止五个 |
| P1-4 | "single-point-of-truth for the W1 results" | EN `:625-634`；ZH `:436` | 仅 13 条重述定理的链，不能覆盖 474 条；可辩护但措辞过强 |

### P2（3 条）

| # | 原句 | 出处 | 说明 |
|---|---|---|---|
| P2-1 | "nine other theorems" | EN `:53-54`；ZH `:39` | 「九条」没有给出清单与计数规则，建议删去数字或附清单 |
| P2-2 | "importing three independently verified modules" | EN `:55-57`；cover letter `:66` | 「independently」易被读成「独立推导」；建议改为 "three modules verified to compile on their own" |
| P2-3 | "`Declaration.lean` ... producing a 33 KB `.olean`" | EN `:587-596`；ZH `:412-420` | 易变数值，建议删除（维护不一致风险） |

**P0 = 8 条。** 其中位于当前投稿材料中的为 P0-1、P0-3、P0-7、P0-8（P0-3 在 cover letter，其余在 tex）；P0-2、P0-4、P0-5、P0-6 来自 README、内部文档或历史表述。另有 N9（现稿 GB 的反向过时陈述）不重复计入 P0。

---

## 6. 汇报摘要

- **三栏条数**：可主张 **13** 条 / 只能条件主张 **11** 条 / 不可主张 **10** 条；合计 **34** 条。
- **P0 风险**：**8 条**，分别是
  1. "a unique prime basis $\{2,3,5,7\}$"
  2. "CSQIT derives 420 / the closure sequence from the axioms"
  3. "two independent derivations converging on the same value"
  4. "A–J formalize discrete causality"
  5. "GenerationBridge compiles without errors"
  6. "curvature_energy is strictly decreasing"
  7. "451 theorems / 28 modules / exactly one sorry"
  8. "All results are formalized in Lean"
- **论文待同步清单**：**26 条**，按文件分组为
  - `paper_revision/csqit_w1_paper.tex`：**12** 条（EN-1～EN-12）
  - `paper_revision/csqit_w1_paper_zh.tex`：**12** 条（ZH-1～ZH-12）
  - `paper_revision/cover_letter.txt`：**2** 条（CL-1～CL-2）
- **最该先改的三句**：
  1. 摘要 `:48`（中文 `:39`）"a unique prime basis $\{2,3,5,7\}$" —— 这是最显眼、最容易被一条 Lean 定理（`prime_solution_lex_min`）直接反驳的句子。
  2. 统计段 `:533-540` / `:613-623`（中文 `:368` / `:434`）"451 theorems, 28 modules, exactly one sorry" —— 纯计数器即可推翻，且 cover letter 同句一并要改。
  3. GB 段 `:598-607`（中文 `:422-428`）"has not been fixed, and the module currently does not compile" —— 与现仓库「墓碑参与构建、0 错误」正面冲突，且与 P0-5 的旧表述方向相反，最容易被审稿人当成「作者不了解自己仓库状态」。

---

## 7. 本台账不证明什么 / 方法限制

- [事实] 本台账未运行 `lake build`；构建事实引自任务简报与既有审计产物 `analysis_axioms.tsv` / `analysis_axioms.log`（474 条审计记录，零 `sorryAx`）。
- [事实] 本台账未修改任何 `.lean`、`.tex`；第 4 节的建议新文全部是**未执行的 patch 清单**。
- [推断] 「推荐替代表述」是编辑建议，不构成新定理；其中涉及「n ≥ 8 递减」的判断只是对 `GenerationBridge.lean` 头注的分析性复述，未形式化。
- [推断] 「P0/P1/P2」分级是本文档的风险判断，不是 Lean 层级的判定；四档数学判定仍以 `DETERMINACY.md` / `LAWS.md` / `BOUNDARIES.md` 为准。
- [事实] 本台账没有新增数学结论，也没有替论文补充任何论证；所有「支撑定理」均指向仓库中已存在、已审计的定理名。

---

## 8. 第十三轮增量（2026-11-07，G12–G17）

> 本节为增量附录，不改变 §0–§7 的 474 条基线；新增定理位于独立模块
> `CSQIT_V1Bridge/StructuralLimits.lean`、`CausalSetWitness.lean`、
> `NonTotalModel.lean`，零新增 axiom、零 sorry。

| # | 主张 | 档位 | 证据 |
|---|---|---|---|
| N1 | 保振幅自映射必为恒等；保振幅参数族作用全平凡 | **A（否定）** | `StructuralLimits.lean` `amplitude_preserving_eq_id`、`amplitude_scale_action_trivial` |
| N2 | AxiomC 模型 `compose` 无条件交换 | **A** | 同文件 `compose_comm_of_axiomC` |
| N3 | 任意层的因果序向上定向、无极大元、每步双前驱 | **A** | 同文件 `layer_upward_directed`、`layer_no_maximal`、`layer_step_two_predecessors` |
| N4 | `input ≡ []`；只经 input 的边界映射必常值、不可单射 | **A（接口否定）** | 同文件 `boundary_input_not_injective`、`boundary_determined_not_injective`、`causal_boundary_determined_not_injective` |
| N5 | 见证模型（`ℕ, a+b+1, exp(i(n+1)π√2)`）的因果序是局部有限严格偏序且为链 | **A（存在性）** | `CausalSetWitness.lean` `witness_is_locallyFiniteCausalSet`、`witnessReach_total` |
| N6 | 存在合法 v23 模型其典范因果序非全序 | **A（否定）** | `NonTotalModel.lean` `pairReach_not_total`、`exists_nontotal_causal_layer` |

**边界注记**（防止过度主张）：

- N1 不构成「RG 流已证否」；只是否定其在振幅层上的最小实现。A2 整体仍 **C**。
- N4 不构成「全息原理已证否」；只是否定 v23 唯一 `input` 通道上的实现。A1 整体仍 **C**。
- N6 不构成「因果性不存在」；只说明线性全局时间不被 v23 强制（**B**：需新增结构后可条件化）。
- A5（测度刚性）本轮无进展，仍为 **C**。

---

## 9. 第十五轮增量（2026-11-07，G18–G23 的新增部分 G20–G23）

> 本节为增量附录，不改变 §0–§8 的 474 条基线；新增定理位于独立模块
> `CSQIT_V1Bridge/GaugeAndEndo.lean`、`OperadImpossibility.lean`，
> 零新增 axiom、零 sorry，`CSQIT_W1` / `CSQIT_Enhanced` 零改动。

| # | 主张 | 档位 | 证据 |
|---|---|---|---|
| N7 | 同一 `compose` 上存在两个合法 `AxiomC`，其振幅与作用量不同；S 不是 compose/因果结构的函数 | **A（否定）** | `GaugeAndEndo.lean` `altAxiomC`、`altAmplitude_zero_ne_witness`、`actionPhase_not_determined_by_compose` |
| N8 | 见证模型自同态全分类为 `φ(n)=φ(0)+n(φ(0)+1)`；保振幅 ⇔ φ=id；`n↦2n+1` 是单射、严格递增、不满射且必改振幅 | **A** | 同文件 `witnessEndo_classification`、`witnessEndo_amplitude_iff`、`witnessEndo_nontrivial_exists` |
| N9 | 结合律使任意有序二叉树装配只依赖叶子数，故有序 operad 不能经 `compose` 忠实嵌入 | **A（否定）** | `OperadImpossibility.lean` `treeEval_eq_power_leafCount`、`no_faithful_ordered_embedding_axiomA` |
| N10 | 任意非平凡 α 上不存在满射 `α → (α → α)`；G3 的 Bool 反例推广到无限载体 | **A（否定）** | 同文件 `no_surjective_self_pi` |

**边界注记**（防止过度主张）：

- N7 不构成「A5 已证否」；它否定的是 A5 的**最小代数翻译**
  （「S 由因果结构决定」）。A5 完整测度论语义仍 **C**。
  它与 G10 相容：G10 的唯一性是「给定 amplitude 之后」。
- N8 不构成「A2 已证否」；它只封死「保 S 的非平凡 compose-自同态」，
  A2 的完整尺度/粗粒化语义仍 **C**。
- N9 不构成「A1 已证否」；它否定的是有序 operad 的 compose 通道，
  A1 的 C*-代数/全息语义仍 **C**。带颜色/多类型的完整 operad 仍为 **B**
  （需新增 operad 类型定义后才可陈述）。
- N10 只覆盖 A2 的**一元翻译**（`End(O)` 读作 `O → O` 全体）；
  V1 A2 原生 operad 语义仍 **C**。

构建验收：`LAKE_JOBS=1 lake build` 全量成功，**2348 jobs**；单进程、无并发。

---

## 10. 第二十二轮增量（2026-11-08，G38–G40）

> 本节为增量附录，不改变 §0–§9 的 474 条基线；新增定理位于独立模块
> `CSQIT_V1Bridge/AmplitudeRigidity.lean`，零新增 axiom、零 sorry，
> `CSQIT_W1` / `CSQIT_Enhanced` 与既有 V1Bridge 文件零改动。

| # | 主张 | 档位 | 证据 |
|---|---|---|---|
| N11 | 组合相等 ⟺ 振幅标签乘积相等；组合被振幅完全决定（同振幅 ⇒ 同 `compose`、同 ρ） | **A（已证）** | `compose_eq_iff_amplitude_mul`、`compose_forced_by_amplitude`、`compose_eq_of_same_amplitude`、`oneStepReach_eq_of_same_amplitude` |
| N12 | `x∘y = x ⟺ amp y = 1`；故因果层存在 ⟺ `1 ∉ range(amp)` | **A（已证）** | `compose_eq_left_iff_amplitude_eq_one`、`exists_compatible_order_iff_amplitude_ne_one` |
| N13 | 同振幅 ⇒ 因果层存在性相同 | **A（已证）** | `compatible_order_exists_iff_of_same_amplitude` |
| N14 | 无限载体上存在「振幅有、因果无」模型（加法模型）；存在「两者皆无」模型（左吸收） | **A（已证）** | `add_amplitude_without_causality`、`leftAbsorbing_no_amplitude_no_layer` |

**边界注记**：

- N11 只钉死 `compose`，不涉及 `input`/`output`；与 G20（同 compose、
  不同 amplitude）不矛盾，二者合起来给出振幅→组合的单向依赖。
- N12 仍是条件于 `AxiomC` 的模型内判据；五字段统一导出因果序仍被
  G1 否定（`NeList` 无振幅却有因果层）。
- N14 是 2×2 四格见证，不是完整分类。V1 A5（测度刚性）仍为 **C**。

构建验收：单模块 242s、0 error；`LAKE_JOBS=1 lake build` 全量
**2357 jobs**、0 error；`#print axioms` 仅 `[propext, Classical.choice,
Quot.sound]`；零 sorryAx。

---

## 11. 第二十四轮增量（2026-11-08，G42–G44）

> 本节为增量附录，不改变 §0–§10 的 474 条基线＋前几轮增量；新增定理位于
> 独立模块 `CSQIT_V1Bridge/FreeModel.lean`、`V23Interface.lean`、
> `OrderMaximality.lean`，零新增 axiom、零 sorry，
> `CSQIT_W1` / `CSQIT_Enhanced` 与既有 V1Bridge 文件零改动。
> 注意：本轮期间工作区存在非本轮的外来改动——7 个 `CSQIT_W1` 文件
> （docstring-only：删除「W1 严格」标签）与未跟踪的
> `CSQIT_Enhanced/PeriodicTable.lean`；后者的 lakefile root 早存在于
> `cd0ab55`，并非本轮新增。这些改动不属于本轮，本轮未提交也未回退。

| # | 主张 | 档位 | 证据 |
|---|---|---|---|
| N15 | 见证模型是单生成元自由半群：任意同态 `φ` 由 `φ 0` 唯一决定，且 `φ n = (φ 0)^(n+1)`；`Hom(见证, C) ≃ C` | **A（已证）** | `composePow_add`、`witnessHom_classification`、`witnessHom_iff_composePow`、`exists_witnessHom_of_element`、`witnessHom_unique_of_zero` |
| N16 | 目标承载 AxiomC 时，沿任意同态振幅是单参数指数：`amp(φ n) = amp(φ 0)^(n+1)` | **A（已证）** | `composePow_amplitude`、`witnessHom_amplitude` |
| N17 | 从见证模型出发的非单射同态必为周期（有限像）；无限载体上的 RG 流必单射 | **A（已证）** | `witnessHom_not_injective_periodic` |
| N18 | v23 有限循环模型 `Fin n`（`n≥1`）可同时实例化 `AxiomA` 与 `AxiomC`（振幅 = 增强层 `cyclicAmplitude`） | **A（已证）** | `instAxiomAFin`、`instAxiomCFin` |
| N19 | `Fin n` 上 `0` 是右作用元；V1 因果-振幅层在 `Fin n` 上**不存在**；故 v23 有限主体上「振幅层可架 ∧ 因果层不可架」 | **A（已证，否定）** | `fin_zero_right_absorbing`、`fin_no_causal_layer`、`v23Finite_amplitude_without_causality`、`fin7_/fin8_...` |
| N20 | 方向相反的两条相容边排除一切共同上界；因此相容序集合一般**无最大元** | **A（已证，否定）** | `no_upper_bound_of_opposite_edges`、`no_maximal_compatible_order`、`pair_two_compatible_orders_opposite` |
| N21 | 「纯 AxiomA ⇒ ρ 全序」为假（乘积模型反例） | **A（已证，元定理）** | `not_universally_total` |

**边界注记**：

- N15/N16 只分类 compose 层；`input`/`output` 已由 AxiomA 强制
  （输入空、输出取后者），未纳入「完整同态」。
- N19 是**否定**，但不是 D 档冲突：本轮不主张 v23 与 V1 矛盾，
  只判定 V1 因果层在 v23 有限主体上不可实例化；振幅层则成功实例化。
- N20/N21 为 V4.0「因果性由 operad 自动保证」的历史降级
  （V7.1.1 改为公理 3）提供形式化根据。
- V1 A1/A2/A5 仍为 **C**；AxiomC 存在性充要条件、G40 四格分类
  仍未闭合。

构建验收：三个新模块均 0 error、0 sorry、0 axiom；`#print axioms`
仅 `[propext, Classical.choice, Quot.sound]`；全量单进程构建结果与
外部并发记录见 `BOUNDARIES.md` §24.6–24.7。

---

## 12. 第二十九轮增量（2026-11-13，PeriodicTable.lean 审计纳入）

> 本节为增量附录，不改变 §0–§11 的基线。对象是 §11 已点名但一直未审计的
> 未跟踪文件 `CSQIT_Enhanced/PeriodicTable.lean`（456 行；构建根
> [lakefile.lean:65](lakefile.lean#L65)，该 root 早于本轮）。本轮只做审计登记，
> 未改动任何定理声明/证明，未 `git add`、未提交。

| # | 主张 | 档位 | 证据 |
|---|---|---|---|
| N22 | 壳层容量满足 `2n² = 2·∑_{l<n}(2l+1)`（"前 n 个奇数之和 = n²"） | **A（已证）** | `shell_capacity_from_quantum_states`（PeriodicTable.lean:119-139）；`shell_capacity`=:84、`angular_momentum_states`=:107 |
| N23 | `ideal_period_length` 只是"存在某周期项使蕴含式成立"的空真命题，**不**主张周期长度 `= 2n²` | **C（不可主张为物理结论）** | 形如 `∃ p ∈ ideal_periods, (p.period_number = n → p.length = 2n²)`（:234-243）；实际长度 2,8,8,18,18,32,32（:230） |
| N24 | `noble_gas_is_balanced_state` 是定义重言（前提即结论） | **C（不可主张）** | `is_noble_gas := is_neutral ∧ is_closed_shell`（:187-188），定理 :279-280 证明为 `:= h` |
| N25 | 头部 `R²=0.957 / 1.8% / 0.91 / 0.013Å` 等数值无任何定理支撑 | **C（无支撑）** | 仅见注释 :34-38、:294-296；无对应 theorem |

**边界注记**：

- N22 是初等算术恒等式（奇数求和），不是从 CSQIT 公理推出的物理结论。
- 该文件三条定理**不使用任何 21 公理类**（`AxiomA`、`AxiomA'`、`AxiomB'`、`AxiomC`、`AxiomC'`、`AxiomJ'`、`AxiomD'` 均未出现）；`#print axioms` 仅 `[propext, Classical.choice, Quot.sound]`。详见 [ANALYSIS_axioms.md](ANALYSIS_axioms.md) §6。
- 无"既有 21 公理类之外的新公理依赖"；此前属**审计口径漏项**，非新公理来源。

**小计**：可主张 1 条（N22，算术恒等式）；不可主张 3 条（N23–N25）。
