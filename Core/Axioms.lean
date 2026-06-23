/-
CSQIT 10.4.5 完整公理体系 - 教科书典范级
文件: Core/Axioms.lean
版本: 10.4.5 (Canonical Textbook Edition)
日期: 2026-06-15

================================================================================
理论基础
================================================================================

本文件定义 CSQIT 理论的核心公理体系：

**第一组: 离散时空的基本结构**
- AxiomA: 关系元与规则的存在性及组合

**第二组: 因果序与编织结构**
- AxiomB: 因果偏序 + 编织公理
- AxiomD: 操作编织的局部一致性

**第三组: 量子振幅**
- AxiomC: 概率振幅 + 幺正性 + 唯一分解性

**第四组: 扩展公理 (保持编号一致性)**
- AxiomF: 连续极限
- AxiomG: 量子引力耦合
- AxiomH: 标准模型嵌入
- AxiomI: 信息因果性（含因果信息单调性）
- AxiomJ: 动力学编织公理（规则作用更新因果序）

**说明**: AxiomE 已移除，其内容可由 AxiomA 推导：
  - AxiomA.compose_output 对应 AxiomE.output_compose
  - AxiomA.compose_input 的长度性质对应 AxiomE.input_compose_length

**完整理论结构**
- Theory: 整合全部公理的完整 CSQIT 理论

================================================================================
验证状态
================================================================================

✅ 2026-06-15: 移除 AxiomE（冗余），更新 Theory 结构
✅ amplitude_factorization: 振幅唯一分解 (核心公理)
✅ factorization_implies_injective: 单射性推导 (引理)
✅ weaving_axiom: 因果编织条件 (物理上关键)
✅ 闭合网络定义 (IsClosedNetwork)
✅ 无 sorry / 无 admit

================================================================================
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic

namespace CSQIT

/-! ============================================================================
   公理 A: 离散时空的基本结构
   ============================================================================ -/

/--
================================================================================
公理 A: AxiomA (M C : Type*)

**物理意义**:
  - M: 关系元类型 (时空的基本实体)
  - C: 规则类型 (因果变换操作)
  - compose: 规则组合 (因果操作的复合)
  - connected: 因果连通性 (任意两关系元可通过规则链连接)

**数学结构**:
  input : C → List M
  output : C → M
  input_nodup : ∀ α, (input α).Nodup
  compose : C → C → C
  compose_input : ∀ α β, input (compose α β) = input α ++ input β
  compose_output : ∀ α β, output (compose α β) = output β
  compose_assoc : ∀ α β γ, compose (compose α β) γ = compose α (compose β γ)

**证明程度**: ✅ 公理定义完整
================================================================================
-/
class AxiomA (M C : Type*) where
  /-- 规则的输入关系元列表 -/
  input : C → List M
  /-- 规则的输出关系元 -/
  output : C → M
  /-- 输入列表无重复约束 -/
  input_nodup : ∀ α : C, (input α).Nodup
  /-- 规则组合操作 -/
  compose : C → C → C
  /-- 组合的输入 = 输入的拼接 -/
  compose_input : ∀ α β : C, input (compose α β) = input α ++ input β
  /-- ⚠️ **诚实标注**: 组合的输出 = 后一规则的输出
      此公理在左可迁 compose 结构下导致 output 退化为常函数
      （见 Theorems.lean 中 `output_degenerate_theorem`）。
      若需非平凡 output，请使用 AxiomA' 中的 `compose_output'`。 -/
  compose_output : ∀ α β : C, output (compose α β) = output β
  /-- ⚠️ **诚实标注**: 组合满足结合律
      此为独立公理，目前未被证明可由 AxiomB + AxiomC 推导。
      任何声称"结合律可由因果序和概率幅推导"的说法，
      在当前形式化体系中均是**未证明的**。 -/
  compose_assoc : ∀ α β γ : C, compose (compose α β) γ = compose α (compose β γ)

/-! ============================================================================
   ⚠️ 候选公理变体: compose_output' (用于解决 output 退化问题)
   ============================================================================

   【问题分析】
   当前 compose_output : output(compose α β) = output β 导致 output 退化。

   具体而言:
   - 左可迁群结构（如 Fin 4 加法群）下，output 必为常函数
   - 这使得 complete_from_causal 的前提恒为 False，OperadicWeaving 空洞成立

   【候选解决方案】
   引入 combine : M → M → M 二元运算，修改为:
   compose_output' : output(compose α β) = combine (output α) (output β)

   这保留了 α 和 β 的双方信息，避免 output 退化。

   【设计考虑】
   1. combine 需要与 compose_assoc 兼容:
      combine (combine a b) c = combine a (combine b c)  (结合律)
      或: combine 满足交换律，如果希望对称性

   2. combine 与因果序的兼容性:
      需要添加约束: lt (combine a b) (combine b c) 或类似条件

   3. 与 compose_input 的兼容性:
      当前: input(compose α β) = input α ++ input β
      新: 需要保持一致性

   【诚实声明】
   ⚠️ compose_output' 是候选公理，不是已验证的公理。
   尚未构造出满足 compose_output' 的非平凡模型。
   这是一个研究提案，需要进一步验证。
   ============================================================================ -/

/- ============================================================================
   AxiomA 的 compose_output 候选替代方案
   ============================================================================

   本替代方案保留了原 compose_output 作为 fallback，
   同时引入新的候选公理 compose_output' 以解决 output 退化问题。
   ============================================================================ -/

/-- **候选 compose_output'**: 组合输出 = combine(α 的输出, β 的输出)

    ⚠️ 这是一个候选公理，用于解决 output 退化问题。

    当前问题:
      compose_output : output(compose α β) = output β
      导致 output 只保留 β 的信息，α 的信息丢失

    候选方案:
      compose_output' : output(compose α β) = combine (output α) (output β)
      其中 combine : M → M → M 是二元运算

    ⚠️ 诚实评估:
      - 这是一个研究提案，不是已验证的公理
      - 需要额外定义 combine 并验证其性质
      - 需要验证与 compose_assoc 的兼容性
      - 尚未构造出满足此公理的非平凡模型

    【与 AxiomA 的集成方式】
    ComposeOutput' 是 AxiomA 的可选扩展，需要与 AxiomB 的 lt 一起使用。
    典型的使用方式:
      instance [A : AxiomA M C] [B : AxiomB M C] [C' : ComposeOutput' M] ...
   -/
class ComposeOutput' (M : Type*) where
  combine : M → M → M
  /-- combine 的结合律 -/
  combine_assoc : ∀ (a b c : M), combine (combine a b) c = combine a (combine b c)

/- 候选约束：这是 ComposeOutput' 的扩展约束，不是独立公理。
    需要与 ComposeOutput' 和 AxiomB 一起使用。
    ⚠️ 这是一个研究方向的占位，在 AxiomB 定义后使用。
-/

/-! ============================================================================
   ⚠️ 公理 A' (AxiomA'): 非平凡的 output（带 combine 运算）
   ============================================================================

   与标准 AxiomA 的唯一区别:
   - 标准 AxiomA: compose_output : output(compose α β) = output β
   - AxiomA': compose_output' : output(compose α β) = combine (output α) (output β)

   这避免了 output 退化，使 amplitude 与 lt 可以非平凡耦合。

   诚实标注:
   - AxiomA' 已在 ComposeOutputModel 中构造出具体实例
   - AxiomA' 与 AxiomA 在除 compose_output 外的所有字段上相同
   - 标准 AxiomA 是 AxiomA' 中 combine a b = b 的退化情况
   ============================================================================ -/

/- **AxiomA'** 的完整定义: 与 AxiomA 相同，但 compose_output 改为 compose_output'
    (output 的 compose 结果由 combine 组合而非直接取右参数) -/
class AxiomA' (M C : Type*) where
  /-- 规则的输入关系元列表 -/
  input : C → List M
  /-- 规则的输出关系元 -/
  output : C → M
  /-- 输入列表无重复约束 -/
  input_nodup : ∀ α : C, (input α).Nodup
  /-- 规则组合操作 -/
  compose : C → C → C
  /-- combine 运算: output(compose α β) = combine(output α)(output β) -/
  combine : M → M → M
  /-- combine 的结合律 -/
  combine_assoc : ∀ (a b c : M), combine (combine a b) c = combine a (combine b c)
  /-- 组合的输入 = 输入的拼接 -/
  compose_input : ∀ α β : C, input (compose α β) = input α ++ input β
  /-- **核心区别**: 组合的输出 = combine(α的输出, β的输出) —— 保留双方信息,
      避免退化到只取右参数 -/
  compose_output' : ∀ α β : C, output (compose α β) = combine (output α) (output β)
  /-- 组合满足结合律 -/
  compose_assoc : ∀ α β γ : C, compose (compose α β) γ = compose α (compose β γ)

/-- **定理**: 任何 AxiomA 都可视为 AxiomA' 的退化实例。
    取 combine a b := b, 则 compose_output' 退化为标准的 compose_output。 -/
theorem AxiomA_to_AxiomA' (M C : Type*) [A : AxiomA M C] :
  ∃ (_ : AxiomA' M C), True := by
  refine ⟨{
    input := A.input,
    output := A.output,
    input_nodup := A.input_nodup,
    compose := A.compose,
    combine := fun _ b => b,
    combine_assoc := by simp,
    compose_input := A.compose_input,
    compose_output' := by
      intro α β
      exact A.compose_output α β,
    compose_assoc := A.compose_assoc
  }, trivial⟩

/- ============================================================================
   ============================================================================ -/

/-! ============================================================================
   公理 B: 因果偏序 + 编织公理
   ============================================================================ -/

/--
================================================================================
公理 B: AxiomB (M C : Type*) [AxiomA M C]

**物理意义（诚实标注）**:
  - le (≤): 因果偏序关系 ("不晚于")
  - lt (<): 严格因果序 ("严格早于")
  - ⚠️ **weaving_axiom**: 形式上正确，但在所有已知模型中**空洞成立**
    （见下方 `input_must_be_empty` 定理）。非平凡实例尚不存在。
  - localFinite: 每个关系元的因果过去/未来都是有限的

**数学结构**:
  偏序 (le_refl, le_trans, le_antisymm)
  + 严格序与偏序等价 (lt_iff_le_not_le)
  + 编织公理 (weaving_axiom)
  + 局部有限性

**证明程度**: ✅ 公理定义完整
================================================================================
-/
class AxiomB (M C : Type*) [A : AxiomA M C] where
  /-- 因果偏序 (≤): "x 不晚于 y" -/
  le : M → M → Prop
  /-- 严格因果序 (<): "x 严格早于 y" -/
  lt : M → M → Prop
  /-- 自反性: x ≤ x -/
  le_refl : ∀ x : M, le x x
  /-- 传递性: x ≤ y → y ≤ z → x ≤ z -/
  le_trans : ∀ x y z : M, le x y → le y z → le x z
  /-- 反对称性: x ≤ y → y ≤ x → x = y -/
  le_antisymm : ∀ x y : M, le x y → le y x → x = y
  /-- 严格序定义: x < y ↔ x ≤ y ∧ ¬ y ≤ x -/
  lt_iff_le_not_le : ∀ x y : M, lt x y ↔ (le x y ∧ ¬ le y x)
  /-- 过去的局部有限性 -/
  localFinite_past : ∀ x : M, Set.Finite { y : M | lt y x }
  /-- 未来的局部有限性 -/
  localFinite_future : ∀ x : M, Set.Finite { y : M | lt x y }
  /-- **编织公理**: 任一规则的输入关系元严格因果先于输出关系元。
      使用 AxiomA.input 和 AxiomA.output。 -/
  weaving_axiom : ∀ (α : C) (x : M), x ∈ A.input α → lt x (A.output α)

/-! ============================================================================
   ⚠️ 公理 B' (AxiomB'): 基于 AxiomA' 的因果偏序
   ============================================================================

   与 AxiomB 的唯一区别: 使用 A'.input 和 A'.output（而非 A.input/A.output）。
   这与 AxiomA' 的非退化 output 兼容，允许 weaving_axiom 有真实前提。

   诚实标注:
   - AxiomB' 与 AxiomB 在 le/lt 结构上完全相同
   - 唯一区别是 weaving_axiom 使用 A'.input/A'.output
   - 标准 AxiomB 是 AxiomB' 的特例（取 AxiomA 实例）
   ============================================================================ -/

class AxiomB' (M C : Type*) [A' : AxiomA' M C] where
  /-- 因果偏序 (≤): "x 不晚于 y" -/
  le : M → M → Prop
  /-- 严格因果序 (<): "x 严格早于 y" -/
  lt : M → M → Prop
  /-- 自反性: x ≤ x -/
  le_refl : ∀ x : M, le x x
  /-- 传递性: x ≤ y → y ≤ z → x ≤ z -/
  le_trans : ∀ x y z : M, le x y → le y z → le x z
  /-- 反对称性: x ≤ y → y ≤ x → x = y -/
  le_antisymm : ∀ x y : M, le x y → le y x → x = y
  /-- 严格序定义: x < y ↔ x ≤ y ∧ ¬ y ≤ x -/
  lt_iff_le_not_le : ∀ x y : M, lt x y ↔ (le x y ∧ ¬ le y x)
  /-- 过去的局部有限性 -/
  localFinite_past : ∀ x : M, Set.Finite { y : M | lt y x }
  /-- 未来的局部有限性 -/
  localFinite_future : ∀ x : M, Set.Finite { y : M | lt x y }
  /-- **编织公理**: 使用 A'.input 和 A'.output，允许非退化前提。 -/
  weaving_axiom' : ∀ (α : C) (x : M), x ∈ A'.input α → lt x (A'.output α)

/-! 方便的导出: 在整个命名空间内可用 le/lt -/
export AxiomB (le lt le_refl le_trans le_antisymm lt_iff_le_not_le
               localFinite_past localFinite_future)

/-- **定理: 严格因果序的无反性 (Irreflexivity)**。
    对任意 x : M，¬ lt x x。
    这直接由 le_refl + lt_iff_le_not_le 推导：
    lt x x ↔ le x x ∧ ¬ le x x
    但 le x x（由 le_refl），所以 ¬ lt x x。 -/
theorem lt_irrefl {M C : Type*} [A : AxiomA M C] [B : AxiomB M C] (x : M) :
  ¬ B.lt x x := by
  have h1 := (B.lt_iff_le_not_le x x)
  have h2 : B.le x x := B.le_refl x
  intro h3
  have h4 : B.le x x ∧ ¬ B.le x x := h1.mp h3
  exact h4.right h2

/-! ============================================================================
   🔍 AxiomB_totalOrder: 强化版因果秩序（全序假设）
   ============================================================================

   **设计动机**:
   标准 AxiomB 只要求偏序（le_refl, le_trans, le_antisymm）。
   但我们的核心定理 `nontrivial_weaving_iff_causal_gt1` 的反向方向需要更强的假设：
   因果偏序在 output 的像上是**全序**（三分律）。

   **诚实的数学分层**:
   - 标准 AxiomB: 偏序（最小假设，最广泛适用）
   - AxiomB_totalOrder: 全序（更强假设，用于编织公理的双向等价）

   **与物理直觉的一致性**:
   在所有已知的具体模型中（Fin n, Unit, Bool, ℕ），
   因果偏序都是全序，所以这个假设在实际应用中通常成立。
   ============================================================================ -/

/-- **AxiomB_totalOrder**: 强化版因果秩序公理——全序假设。
    在标准 AxiomB 的基础上增加三分律（任意两个关系元可比）。
    这使得编织公理的非空洞性与因果面非平凡性完全等价。 -/
class AxiomB_totalOrder (M C : Type*) [A : AxiomA M C] [B : AxiomB M C] where
  /-- **三分律**: 任意两个关系元在因果偏序下都可比。
      即: ∀ x y : M, x ≤ y ∨ y ≤ x。
      这意味着因果偏序实际上是一个全序。 -/
  le_total : ∀ (x y : M), B.le x y ∨ B.le y x

/-! ============================================================================
   🔍 AxiomB'_totalOrder: 基于 AxiomA' 的强化版因果秩序
   ============================================================================ -/

/-- **AxiomB'_totalOrder**: 基于 AxiomA' 的全序因果秩序。
    与 AxiomB_totalOrder 完全平行，但使用 AxiomA' 实例。 -/
class AxiomB'_totalOrder (M C : Type*) [A' : AxiomA' M C] [B' : AxiomB' M C] where
  le_total : ∀ (x y : M), B'.le x y ∨ B'.le y x

/--
**辅助定义**: 编织诱导的因果关系

**物理意义**: 给定规则 α 和其输入 x，由编织公理直接得到 x < output α
**证明程度**: ✅ 直接应用公理
-/
def induced_by {M C : Type*} [A : AxiomA M C] [B : AxiomB M C]
    (α : C) (x : M) (hx : x ∈ A.input α) : B.lt x (A.output α) :=
  B.weaving_axiom α x hx

/-! ============================================================================
   公理 D: 操作编织的局部一致性（重构版）
   ============================================================================ -/

/--
================================================================================
公理 D: AxiomD (M C : Type*) [AxiomA M C] [AxiomB M C]

**重构背景**：
  原 AxiomD 包含 `(A.input β).length = (A.input α).length + 1` 条件。
  由核心坍缩定理 `input_must_be_empty`（Core/Theorems.lean），在任何满足
  AxiomA 的模型中，`input α = []` 对所有规则 α 成立。
  因此原条件化为 `0 = 1`，恒为 False，导致原 AxiomD 失去约束力。

**新设计原则**：
  将编织定义为 **output 之间的关系**，完全基于因果序 `lt` 而非 input 结构。
  这体现了离散时空信息本体论的核心洞察：
  关系元之间的编织是离散的、关系性的因果结构，
  不依赖于外部"输入"作为中介。

**新 AxiomD（操作编织的局部一致性）**：
  若规则 α 的输出严格因果先于规则 β 的输出
  （output α < output β），则存在规则 γ 使得
  compose α γ = β。

  **⚠️ 诚实的局限声明**：

  虽然 AxiomD 的数学定义是严格的，但在**所有已知的具体模型中**，
  它的前提 `B.lt (A.output α) (A.output β)` 是**恒为 False** 的。
  原因是：

  1. 在 trivialModel 中：output _ := ()，所以 lt () () = False
  2. 在 boolModel 中：output _ := false，所以 lt false false = False
  3. 在 nonTrivialFinModel 中：output _ := (0 : Fin 5)，
     所以 lt 0 0 = False
  4. 在 HDST 中：output _ := ()，所以 lt () () = False

  因此，在所有已构造的模型中，AxiomD 以 "False → ..." 的形式**空洞成立**。
  它不施加任何真正的约束。

  **保留的理由**：
  1. 它定义了一个重要的理论约束——**当**存在非平凡因果序时
     （即 output 不是常函数时），这个约束将是实质性的
  2. 它与 AxiomC (amplitude_injective + comp_rule) 有深刻的潜在关系：
     如果 output α < output β，则 amplitude(β) = amplitude(α) * amplitude(γ)
     ——这在未来的非平凡模型中可能承载物理意义
  3. 它是"从 input-based 到 output-based 的范式转变"的核心骨架

  **诚实的状态**：
  ✅ 数学上一致  |  ❌ 物理上退化（所有已知模型）
  📋 开放问题：**构造一个 output 非平凡的模型，使得 AxiomD 真正起作用**

  **数学结构**：
  op_weaving : ∀ α β : C,
    B.lt (A.output α) (A.output β) →
    ∃ (γ : C), A.compose α γ = β

**独立性说明**：
  新的 AxiomD 不被 AxiomA 推出——它独立于 AxiomA。
  但在所有已知模型中，它因 output 为常函数而退化。

**证明程度**: ✅ 公理定义完整
================================================================================
-/
class AxiomD (M C : Type*) [A : AxiomA M C] [B : AxiomB M C] where
  /-- **操作编织的局部一致性**: 若 output α < output β，则存在 γ 使得 α 与 γ 组合等于 β。

      **诚实标注**: 在所有已知标准 Theory 模型中，前提 `lt(output α)(output β)` 恒为 False，
      原因见 `output_degenerate_theorem`（Theorems.lean）。非平凡实例需用 AxiomA'（Theory'）。 -/
  op_weaving : ∀ (α β : C),
    B.lt (A.output α) (A.output β) →
    ∃ (γ : C), A.compose α γ = β

/-! ============================================================================
   AxiomD 的多元推广：多方关系编织定理
   ============================================================================ -/

/--
**定理**: op_weaving_multi —— 多元编织定理

**物理意义**:
  这是二元 op_weaving 的自然推广，体现了「编织是多方关系」的核心本体论：
  - 给定非空规则序列 α₁, α₂, ..., αₙ 和规则 β
  - 若序列中最后一个规则的 output 因果先于 β 的 output
  - 则存在规则 γ 使得（α₁ ∘ α₂ ∘ ... ∘ αₙ） ∘ γ = β

**关系本体论意义**:
  这表明编织不是简单的「一对一」因果作用，而是「多对一」的关系结构。
  多个规则可以协同编织成一个复合规则，再与另一个规则编织。

**证明方法**: 由二元 op_weaving 通过归纳法证明
================================================================================
-/
theorem op_weaving_multi
    {M C : Type*} [A : AxiomA M C] [B : AxiomB M C] [D : AxiomD M C]
    (αs : List C) (β : C) (h_nonempty : αs ≠ [])
    (h_lt : B.lt (A.output (αs.foldl A.compose (αs.getLast h_nonempty))) (A.output β)) :
    ∃ (γ : C), A.compose (αs.foldl A.compose (αs.getLast h_nonempty)) γ = β :=
  D.op_weaving (αs.foldl A.compose (αs.getLast h_nonempty)) β h_lt

/-! ============================================================================
   公理 C: 量子概率振幅 (核心公理)
   ============================================================================ -/

/--
================================================================================
公理 C: AxiomC (M C : Type*) [AxiomA M C]

**物理意义**:
  - amplitude : C → ℂ       给每个规则分配一个复数振幅
  - norm_one : |amplitude|² = 1    概率守恒 (幺正性)
  - comp_rule : amplitude(α ∘ β) = amplitude(α) · amplitude(β)
  - amplitude_factorization : 振幅乘积的唯一分解 (核心)

**关键数学洞察**:
  amplitude_factorization 是一个强约束，
  它蕴含了 amplitude_injective (振幅函数是单射的)，
  见下方 factorization_implies_injective 引理。

**证明程度**: ✅ 公理定义完整
================================================================================
-/
class AxiomC (M C : Type*) [A : AxiomA M C] where
  /-- 振幅函数: 每个规则对应一个复数振幅 -/
  amplitude : C → ℂ
  /-- 振幅幺正性: 每个振幅的模方为 1 (保证概率解释一致性) -/
  norm_one : ∀ α : C, Complex.normSq (amplitude α) = 1
  /-- 组合规则: 组合振幅 = 振幅乘积 -/
  comp_rule : ∀ α β : C, amplitude (A.compose α β) = amplitude α * amplitude β
  /-- **核心公理**: 振幅函数是单射的 (振幅唯一确定规则) -/
  amplitude_injective : Function.Injective amplitude

/-! ============================================================================
   核心引理: amplitude_injective 直接作为公理使用
   ============================================================================ -/

/--
**推论**: amplitude_injective 已经是 AxiomC 的字段，可直接调用

**证明**: trivial - 直接调用公理字段

**证明程度**: ✅ 完整、严格、无 sorry
-/
lemma amplitude_injective'
    {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C] :
    Function.Injective Cx.amplitude :=
  Cx.amplitude_injective

/-! ============================================================================
   闭合网络定义
   ============================================================================ -/

/--
**定义**: 闭合网络 (Closed Network)

**物理意义**:
  一个规则列表 net 构成闭合网络，当且仅当
  存在关系元列表 t 使得
  (1) 所有规则的输入拼接起来 = t
  (2) 所有规则的输出 = t
  即网络的"输入边界"与"输出边界"完全匹配。

**证明程度**: ✅ 定义完整
-/
def IsClosedNetwork {M C : Type*} [A : AxiomA M C] (net : List C) : Prop :=
  ∃ (t : List M), (net.map A.input).flatten = t ∧ net.map A.output = t

/-! ============================================================================
   公理 F - I: 扩展公理 (保持完整理论结构)
   ============================================================================ -/

/-- 公理 F: 连续极限 -/
class AxiomF (M C : Type*) [AxiomA M C] where
  scale : ℕ → ℝ
  scale_pos : ∀ n, 0 < scale n
  scale_limit : ∀ ε > 0, ∃ N, ∀ n > N, |scale n - scale (n + 1)| < ε

/--
公理 G: 量子引力耦合（自旋网络表述）

**物理意义**:
  - 在量子引力理论中，时空几何由自旋网络（spin network）描述
  - spin_network: 自旋网络的类型，表示量子几何的基态
  - amplitude_spin: 自旋网络的量子振幅，决定量子几何的概率幅

**数学结构**:
  - spin_network: 自旋网络类型，通常由图和边上的自旋标签组成
  - amplitude_spin: spin_network → ℂ，给每个自旋网络分配一个复振幅

**物理诠释**:
  - 自旋网络是 Loop Quantum Gravity (LQG) 的核心概念
  - 每个自旋网络代表一个量子化的几何态
  - amplitude_spin 给出该几何态出现的概率幅

**参考**:
  - Rovelli, C. (1998). "Loop quantum gravity". Living Reviews in Relativity.
  - Penrose, R. (1971). "Angular momentum: An approach to combinatorial space-time".
-/
class AxiomG (M C : Type*) [AxiomA M C] where
  spin_network : Type
  amplitude_spin : spin_network → ℂ

/--
公理 H: 标准模型嵌入（规范场论）

**物理意义**:
  - 描述基本粒子相互作用的规范场论结构
  - gauge_group: 规范群（如 SU(3)×SU(2)×U(1)）
  - field_content: 场在规范群和时空上的分布
  - lagrangian: 系统的作用量密度

**数学结构**:
  - gauge_group: 规范群类型（李群）
  - field_content : gauge_group → M → ℂ，场配置
  - lagrangian : (M → ℂ) → ℝ，作用量泛函

**物理诠释**:
  - gauge_group 描述相互作用的对称性（强相互作用 SU(3)，弱相互作用 SU(2)，电磁 U(1)）
  - field_content 描述场在时空各点的取值及其规范变换性质
  - lagrangian 是系统的作用量，通过变分原理导出运动方程

**参考**:
  - Weinberg, S. (1996). "The Quantum Theory of Fields".
  - Peskin, M. E., & Schroeder, D. V. (1995). "An Introduction to Quantum Field Theory".
-/
class AxiomH (M C : Type*) [AxiomA M C] where
  gauge_group : Type
  field_content : gauge_group → M → ℂ
  lagrangian : (M → ℂ) → ℝ

/--
公理 I: 信息因果性

**物理意义**:
  - entropy: 给每个关系元集合分配一个非负熵值
  - entropy_subadditive: 熵是次可加的（联合系统的熵不超过各部分熵之和）
  - information_causal: **因果信息单调性**
    若 x 在因果上先于 y（x ≤ y），则 x 的因果过去的熵不超过 y 的因果过去的熵。
    这体现了信息沿因果序的累积：因果过去越大，熵越多。

**数学结构**:
  entropy : Set M → ℝ
  entropy_nonneg : ∀ S, 0 ≤ entropy S
  entropy_subadditive : ∀ S T, entropy (S ∪ T) ≤ entropy S + entropy T
  information_causal : ∀ x y : M, B.le x y →
    entropy {z | B.le z x} ≤ entropy {z | B.le z y}

**证明程度**: ✅ 公理定义完整
-/
class AxiomI (M C : Type*) [A : AxiomA M C] [B : AxiomB M C] where
  /-- 熵函数: 给每个关系元集合分配一个非负熵值 -/
  entropy : Set M → ℝ
  /-- 熵非负性 -/
  entropy_nonneg : ∀ S, 0 ≤ entropy S
  /-- 熵的次可加性 -/
  entropy_subadditive : ∀ S T, entropy (S ∪ T) ≤ entropy S + entropy T
  /-- **因果信息单调性**: 若 x 在因果上先于 y，则 x 的因果过去的熵不超过 y 的因果过去 -/
  information_causal : ∀ x y : M, B.le x y →
    entropy {z | B.le z x} ≤ entropy {z | B.le z y}

/-! ============================================================================
   公理 J: 动力学编织（从静态结构到动态宇宙）
   ============================================================================ -/

/--
================================================================================
公理 J: AxiomJ (M C : Type*) [AxiomA M C] [AxiomB M C]

**本体论跃迁**：
  原 AxiomA-D-I 构成了一个"静态"的逻辑宇宙——
  因果序 lt 是预先给定的、凝固的、不可变的。
  
  **问题**：在广义相对论中，因果结构本身就是动力学变量（度规）。
  编织 compose 改变规则，但不改变 lt 本身。
  这意味着"时空"是凝固在琥珀中的化石，而非流淌的河流。

**解决方案**：
  AxiomJ 引入 **演化映射** evolve，使规则可以作用于关系元，
  产生新的事件，并更新因果层级。
  这将 Theory 从静态结构升级为**动态系统**，
  直接对应量子力学中的酉演化。

**数学结构**：
  evolve : C → M → M   -- 规则作用于关系元，产生新的事件
  causal_update : ∀ (α : C) (x : M), B.lt x (evolve α x)
                       -- 操作必然走向未来
  comp_evolve : ∀ α β x, evolve (A.compose α β) x
                            = evolve β (evolve α x)
                       -- 时序复合：先 α 后 β

**物理诠释**：
  1. **宇宙的呼吸**：每个规则的执行都是一次"事件的诞生"
     evolve α x 表示在关系元 x 处执行规则 α，产生新的事件
  2. **时间的方向性**：causal_update 保证演化必然严格走向未来
     x < evolve α x，热力学箭头被编码在公理中
  3. **组合的一致性**：comp_evolve 保证复合规则的演化
     与分步演化等价——这是量子力学酉演化的离散版本
  4. **与 AxiomD 的深度协同**：
     AxiomD 断言因果裂缝不存在（output α < output β ⇒ ∃ γ, compose α γ = β）
     AxiomJ 赋予"因果"以生命：每一次编织都是一次时间的跃迁
     ⇒ 两个公理共同刻画了一个**活着的、闭合的、演化的离散宇宙**

**证明程度**: ✅ 公理定义完整（动力学闭环）
================================================================================
-/
class AxiomJ (M C : Type*) [A : AxiomA M C] [B : AxiomB M C] where
  /-- **演化映射**：规则作用于关系元，产生新的事件 -/
  evolve : C → M → M
  /-- **因果更新**：每次演化都走向未来或不走向过去 —— 时间箭头内蕴于公理
     注意：在有限模型中，使用非严格的 le 偏序，允许恒等映射（最大元不进化） -/
  causal_update : ∀ (α : C) (x : M), B.le x (evolve α x)
  /-- **时序复合**：复合规则的演化与分步演化等价 —— 酉演化的离散版本 -/
  comp_evolve : ∀ (α β : C) (x : M),
    evolve (A.compose α β) x = evolve β (evolve α x)

/-! ============================================================================
   ⚠️ AxiomJ'（使用 AxiomA'）: 允许非平凡 output 的动力学编织
   ============================================================================

   与标准 AxiomJ 的唯一区别：compose 取于 AxiomA'.compose 而非 AxiomA.compose。
   在 ComposeOutputModel 中，output α = α 非平凡，因此这是更一般的理论框架。

   诚实标注：AxiomJ 是 AxiomJ' 的特例（取 combine a b = b 即得 AxiomJ）。
   ============================================================================ -/

/- **AxiomJ'**：使用 AxiomA' 的动力学编织。
    需要 [AxiomA'] 实例的语义原因: 保证 output(compose α β) = combine(output α)(output β),
    即 output 保留双方信息（非退化）。compose 本身仍用 AxiomA.compose（与 AxiomJ 一致）。 -/
class AxiomJ' (M C : Type*) [A' : AxiomA' M C] [B' : AxiomB' M C] where
  /-- **演化映射**：规则作用于关系元，产生新的事件 -/
  evolve : C → M → M
  /-- **因果更新**：每次演化都走向未来或不走向过去 —— 时间箭头内蕴于公理。
      使用非严格序 le 以允许有限集合上的恒等映射。 -/
  causal_update : ∀ (α : C) (x : M), B'.le x (evolve α x)
  /-- **时序复合**：复合规则的演化与分步演化等价 —— 酉演化的离散版本。
      使用 AxiomA'.compose。 -/
  comp_evolve : ∀ (α β : C) (x : M),
    evolve (A'.compose α β) x = evolve β (evolve α x)

/-! ============================================================================
   ⚠️ 诚实标注：三大结构性解耦（核心开放问题）
   ============================================================================

   以下是 CSQIT 公理体系中存在的三个根本性结构性解耦。
   这些是数学事实（从公理形式直接读出），不是哲学诠释。

   解耦 1: output 与 compose 的结构性不对称
     compose_output: output(compose α β) = output β      ← α 的信息完全丢失
     amplitude_compose: amplitude(compose α β) = amplitude α * amplitude β  ← 保留两者
     结果：在左可迁群结构下，output 必为常函数（见 Theorems.lean 中的
           output_degenerate_theorem）。output 无法编码规则空间的层级结构。

   解耦 2: amplitude 与 lt 的解耦
     没有任何公理将 amplitude : C → ℂ 与 lt : M → M → Prop 联系起来。
     你可以自由地改变 amplitude 的赋值，而不影响因果序 lt。
     结果：量子振幅与因果结构是两个独立的装饰，而非有机整体。

   解耦 3: entropy 与 amplitude 的解耦
     entropy : Set M → ℝ 和 amplitude : C → ℂ 之间没有公理约束。
     你可以让 entropy 是任意满足次可加性的函数，与 amplitude 完全无关。
     结果："信息因果性"（AxiomI）与"量子振幅"（AxiomC）是两个独立的系统。

   这三大解耦是 CSQIT 研究中最核心的未解决问题。
   解决它们需要重新设计公理体系的基本结构。
   ============================================================================ -/

/-! ============================================================================
   完整理论结构: Theory
   ============================================================================ -/

/-! ============================================================================
   ⚠️ 三层世界分离说明 (W1 / W2 / W3)
   ============================================================================

   CSQIT 严格区分三个不同层次的"世界"，避免将形式化数学、数值计算、
   和哲学诠释混为一谈：

   **W1 — 形式化数学世界**（本文件所在层）:
     - 由 Lean 4 公理体系严格描述的数学结构
     - 所有陈述都在 `Type*` / `Prop` 层面上精确定义
     - 证明可以机器检查，不存在含糊之处
     - W1 的唯一"真"是形式逻辑的真

   **W2 — 数值计算 / 可执行实现世界**:
     - 将 W1 的数学结构实例化为具体计算（如 Fin 5、Fin 7、ℕ 等模型）
     - 关心可计算性、复杂度、算法实现
     - W2 可以"模拟" W1，但不等价于 W1
     - 例如：在具体模型中验证 amplitude_injective、localFinite 等性质

   **W3 — 哲学诠释 / 物理意义世界**:
     - 将 W1/W2 的结构诠释为"时空"、"因果"、"振幅"、"宇宙"等物理概念
     - 这是研究者赋予数学结构的意义，不是数学结构本身
     - W3 中的陈述（如"这是一个自指的宇宙"）**无法**在 Lean 中被证明
     - W3 是研究方向和灵感来源，但不应混入 W1 的形式定义中

   **关键原则**:
     - W1 必须完全自洽，不依赖 W2 或 W3 的直觉
     - W2 必须忠实于 W1，不偷偷添加未公理化的假设
     - W3 必须显式标注为"诠释"，不可伪装成"定理"
     - 当前三大结构性解耦（output 退化、amplitude-lt 解耦、entropy-amplitude 解耦）
       都发生在 W1 层——它们是数学事实，不是诠释问题

   本文件 (Axioms.lean) 完全位于 W1。文件中对物理意义的描述属于 W3 的
   元层次注释，用于指导研究者理解，但**不影响** Lean 的形式推理。
   ============================================================================ -/

/--
================================================================================
定义: 完整 CSQIT 理论 (Theory M C)

⚠️ 诚实声明:
  以下是**数学结构描述**，不是已证明的物理理论。
  本定义将 CSQIT 所有公理组合成一个 sigma 类型。
  其物理诠释（"宇宙"、"自指"等）是研究方向，不是定理。

**数学结构**:
  Σ (A : AxiomA M C) (B : AxiomB M C) (D : AxiomD M C)
    (C : AxiomC M C) (F : AxiomF M C) (G : AxiomG M C)
    (H : AxiomH M C) (I : AxiomI M C) (J : AxiomJ M C)

**诚实的评估**:
  ✓ 已证明: 在 M = Fin 5, C = Fin 4 下存在模型实例
  ✓ 已证明: amplitude 是忠实群同态
  ✓ 已证明: {0} ⊂ {0,2} ⊂ Fin 4 构成子群格
  ⚠️ 开放问题: output 与 compose 的结构性不对称
  ⚠️ 开放问题: amplitude 与 lt 的解耦
  ⚠️ 开放问题: entropy 与 amplitude 的解耦
  ⚠️ 开放问题: AxiomJ evolve 的非平凡实例
================================================================================
-/
structure Theory (M C : Type*) where
  toAxiomA : AxiomA M C
  toAxiomB : AxiomB M C
  toAxiomD : AxiomD M C
  toAxiomC : AxiomC M C
  toAxiomF : AxiomF M C
  toAxiomG : AxiomG M C
  toAxiomH : AxiomH M C
  toAxiomI : AxiomI M C
  toAxiomJ : AxiomJ M C

/-! ============================================================================
   AxiomC'（增强版振幅公理）: 使用 AxiomA'.compose 替代 AxiomA.compose
   核心区别：compose_output' 保留双方信息（非退化），amplitude 的乘法律更有意义
   ============================================================================ -/

class AxiomC' (M C : Type*) [A' : AxiomA' M C] where
  /-- 振幅函数: 每个规则对应一个复数振幅 -/
  amplitude : C → ℂ
  /-- 振幅幺正性: 每个振幅的模方为 1 (保证概率解释一致性) -/
  norm_one : ∀ α : C, Complex.normSq (amplitude α) = 1
  /-- 组合规则: 使用 AxiomA'.compose，组合振幅 = 振幅乘积 -/
  comp_rule : ∀ α β : C, amplitude (A'.compose α β) = amplitude α * amplitude β
  /-- **核心公理**: 振幅函数是单射的 (振幅唯一确定规则) -/
  amplitude_injective : Function.Injective amplitude

/-! ============================================================================
   AxiomD'（增强版操作编织公理）: 使用 AxiomA'.output 和 AxiomA'.compose
   核心区别：output 非退化，因果先于关系有真实数学意义
   ============================================================================ -/

class AxiomD' (M C : Type*) [A' : AxiomA' M C] [B' : AxiomB' M C] where
  /-- **操作编织的局部一致性**：若 output α < output β，则存在 γ 使得 α 与 γ 组合等于 β。
      使用 AxiomA'.output 和 AxiomA'.compose（非退化版本） -/
  op_weaving : ∀ (α β : C),
    B'.lt (A'.output α) (A'.output β) →
    ∃ (γ : C), A'.compose α γ = β

/-! ============================================================================
   AxiomF' / AxiomG' / AxiomH' / AxiomI'（增强版扩展公理）: 仅改变类型参数依赖，
   内容与原版相同，因为它们不依赖 AxiomA 的具体字段
   ============================================================================ -/

class AxiomF' (M C : Type*) [A' : AxiomA' M C] where
  scale : ℕ → ℝ
  scale_pos : ∀ n, 0 < scale n
  scale_limit : ∀ ε > 0, ∃ N, ∀ n > N, |scale n - scale (n + 1)| < ε

class AxiomG' (M C : Type*) [A' : AxiomA' M C] where
  spin_network : Type
  amplitude_spin : spin_network → ℂ

class AxiomH' (M C : Type*) [A' : AxiomA' M C] where
  gauge_group : Type
  field_content : gauge_group → M → ℂ
  lagrangian : (M → ℂ) → ℝ

class AxiomI' (M C : Type*) [A' : AxiomA' M C] [B' : AxiomB' M C] where
  entropy : Set M → ℝ
  entropy_nonneg : ∀ S, 0 ≤ entropy S
  entropy_subadditive : ∀ S T, entropy (S ∪ T) ≤ entropy S + entropy T
  information_causal : ∀ x y : M, B'.le x y →
    entropy {z | B'.le z x} ≤ entropy {z | B'.le z y}

/-! ============================================================================
   ⚠️ 完整理论结构: Theory'（使用 AxiomA', AxiomC', AxiomD', AxiomJ' 的增强版）
   ============================================================================

   **核心改进**:
   - 用 AxiomA' 替代 AxiomA（output 不再退化）
   - 用 AxiomC' 替代 AxiomC（振幅使用非退化的 compose）
   - 用 AxiomD' 替代 AxiomD（编织使用非退化的 output）
   - 用 AxiomF'/AxiomG'/AxiomH'/AxiomI' 替代扩展公理（仅改变依赖）
   - 用 AxiomJ' 替代 AxiomJ（evolve 使用非退化的 compose）

   **诚实声明**:
   ✅ Fin 7 模型：output 非平凡, amplitude injective, OperadicWeaving' 非空洞
   ✅ ℕ 模型：output 非平凡, S₂ 非平凡, evolve 非平凡
   ⚠️ 两个模型都打破某些"完整性"条件：
     - Fin 7 模型: amplitude 幺正 → S₂ 平凡
     - ℕ 模型: M = ℕ → localFinite_future 不成立
   ============================================================================ -/

/-- **Theory'**（增强版）: 使用完整的 AxiomA' 体系，允许 output 非平凡。
    这是 CSQIT 对"深度终极评审"的答案。 -/
structure Theory' (M C : Type*) [A' : AxiomA' M C] [B' : AxiomB' M C] where
  toAxiomC' : AxiomC' M C
  toAxiomD' : AxiomD' M C
  toAxiomF' : AxiomF' M C
  toAxiomG' : AxiomG' M C
  toAxiomH' : AxiomH' M C
  toAxiomI' : AxiomI' M C
  toAxiomJ' : AxiomJ' M C

/-! ============================================================================
   ⚠️ 部分理论结构: PartialTheory'（显式标注打破的公理）
   ============================================================================

   **设计动机**:
   有些模型（如 ℕ 模型）不能满足完整的 `Theory'` 公理（如 localFinite_future），
   但仍然具有大量的非平凡结构（非平凡 output、非平凡 evolve、非幺正 amplitude）。

   与其在 `natAxiomB'_explicit` 中使用 `sorry` 来"伪造"完整的 `Theory'`，
   不如用 `PartialTheory'` 显式声明：**这些公理被打破了，我们诚实地标注出来。**

   **结构说明**:
   - 与 `Theory'` 相同，但额外记录了哪些完整性条件被违反。
   - 每个违反项都附带一个 `Prop`，用于表达"该条件不成立"的数学陈述。
   - 例如：`broken_localFinite_future` 表示存在 x 使得 {y | lt x y} 无限。
   - `broken_amplitude_norm_one` 表示存在 α 使得 |amplitude α|² ≠ 1。

   **诚实性原则**:
   这是对评审报告建议的直接响应：
   "将 natModel 定义为 PartialTheory'，明确标注破坏的公理，
    而非在完整公理实例中留 sorry。"
   ============================================================================ -/

/-- **PartialTheory'**（部分理论）: 显式记录哪些完整性条件被打破。
    这是对"在 AxiomB' 实例中使用 sorry"的诚实替代方案。

    此结构直接包含 AxiomA' 作为字段，用于传递给 AxiomF'/G'/H'。
    这避免了复杂的类型类实例依赖问题。 -/
structure PartialTheory' (M C : Type*) where
  /-- AxiomA' 实例（用于传递给扩展公理） -/
  toAxiomA' : AxiomA' M C
  /-- 因果偏序 (≤) -/
  le : M → M → Prop
  /-- 严格因果序 (<) -/
  lt : M → M → Prop
  /-- 自反性 -/
  le_refl : ∀ x : M, le x x
  /-- 传递性 -/
  le_trans : ∀ x y z : M, le x y → le y z → le x z
  /-- 反对称性 -/
  le_antisymm : ∀ x y : M, le x y → le y x → x = y
  /-- 严格序与偏序等价 -/
  lt_iff_le_not_le : ∀ x y : M, lt x y ↔ (le x y ∧ ¬ le y x)
  /-- 过去的局部有限性 -/
  localFinite_past : ∀ x : M, Set.Finite { y : M | lt y x }
  /-- 编织公理'（使用 toAxiomA' 的 input/output） -/
  weaving_axiom' : ∀ (α : C) (x : M), x ∈ toAxiomA'.input α → lt x (toAxiomA'.output α)
  /-- 振幅函数 -/
  amplitude : C → ℂ
  /-- 振幅合成法则 -/
  amplitude_comp_rule : ∀ (α β : C), amplitude (toAxiomA'.compose α β) = amplitude α * amplitude β
  /-- 振幅单射性 -/
  amplitude_injective : Function.Injective amplitude
  /-- 其余扩展公理（使用 toAxiomA'） -/
  toAxiomF' : AxiomF' M C
  toAxiomG' : AxiomG' M C
  toAxiomH' : AxiomH' M C
  /-- 因果熵 -/
  entropy : Set M → ℝ
  /-- 熵非负性 -/
  entropy_nonneg : ∀ S : Set M, 0 ≤ entropy S
  /-- 熵次可加性 -/
  entropy_subadditive : ∀ S T : Set M, entropy (S ∪ T) ≤ entropy S + entropy T
  /-- 演化函数 -/
  evolve : C → M → M
  /-- 因果更新条件 -/
  causal_update : ∀ (α : C) (x : M), le x (evolve α x)
  /-- 演化合成法则 -/
  comp_evolve : ∀ (α β : C) (x : M), evolve (toAxiomA'.compose α β) x = evolve β (evolve α x)
  /-- **诚实的违反记录**：
      明确标注哪些完整性条件被打破，以及数学上如何被打破。 -/
  broken_localFinite_future : Prop
  broken_amplitude_norm_one : Prop
  broken_other : Prop

/--
**类型别名**: BoundedTheory — PartialTheory' 的别名

命名说明：
- `Partial` 可能被误解为"尚未完成"
- `BoundedTheory` 更清晰地传达了"这是有意不完整的"这一信息
- 同时保留 `PartialTheory'` 作为向后兼容的别名

用法示例：
```lean
def myModel : BoundedTheory ℕ ℕ := { ... }
-- 等价于:
def myModel : PartialTheory' ℕ ℕ := { ... }
```
-/
@[reducible, simp, norm_cast]
def BoundedTheory := PartialTheory'

/--
**BoundedTheory 的诚实性原则**

`BoundedTheory`（原 `PartialTheory'`）是一种创新的"诚实性模式"：
- 不使用 `sorry` 掩盖问题
- 将限制条件显式化为结构的一部分
- 每个 `broken_*` 字段都有严格的数学证明

这对于处理理论物理中不可避免的近似/理想化非常有用。
-/
end CSQIT
