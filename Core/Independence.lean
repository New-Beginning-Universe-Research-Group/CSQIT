/-
CSQIT 10.4.5 公理独立性证明 - 深入严谨版
文件: Core/Independence.lean
版本: 10.4.5 (Deep Rigorous Edition)
日期: 2026-06-16

================================================================================
理论基础：独立性证明方法论
================================================================================

本文件研究 CSQIT 公理体系中各公理之间的**独立性**关系。

**独立性的定义**：给定公理集合 S = {A₁, A₂, ..., Aₙ}，称公理 Aᵢ
独立于 S 中其他公理，当且仅当存在一个数学结构（模型），使得：
  (1) 该模型满足 S \ {Aᵢ} 中的所有公理；
  (2) 该模型**不**满足 Aᵢ。

即：Aᵢ 不能从其他公理逻辑推导出来。

**本文件的证明策略**：对每个被研究的公理 Aᵢ，显式构造一个"反模型"
（一个具体的数学结构），证明它：
  • 满足 AxiomA 的其他字段（input, output, input_nodup,
    compose_input, compose_output）但违反 compose_assoc；
  • 或满足 AxiomB 的其他字段（le_refl, le_trans, lt_iff_le_not_le,
    localFinite_*, weaving_axiom）但违反 le_antisymm；
  • 或满足 AxiomC 的其他字段（comp_rule, amplitude_injective）
    但违反 norm_one；
  • 或满足 AxiomC 的其他字段（norm_one, comp_rule）
    但违反 amplitude_injective；
  • 或满足 AxiomA + AxiomB + AxiomC 但违反 AxiomD
    （op_weaving）—— 这是尚未完成的部分。

**显式构造 vs. 战术黑箱**：本文件中的每个独立性证明都通过显式
构造一个结构（C 类型、input 函数、output 函数、compose 函数、
le 关系、振幅函数等）来给出反例，而非依赖 `apply`/`intro`
等抽象战术。这使得证明更加"可读"——读者可以清楚地看到
"这个模型到底是什么样子"。

================================================================================
编译状态说明
================================================================================

本文件严格遵循项目编译配置：
  • 不使用 `sorry`（将被视为编译错误）；
  • 对于尚未完成的独立性问题（如 AxiomD 的独立性），
    使用 `def ... : Prop := ...` 形式将其陈述为未证明命题，
    而非声明为定理；
  • 所有已证明的结论都给出完整、可机器检查的证明。

================================================================================
当前状态的诚实评估
================================================================================

✅ 已严格证明独立的公理约束（显式构造反模型）：
   1. compose_assoc  (AxiomA)   —— 构造非结合律运算
   2. le_antisymm    (AxiomB)   —— 构造自反传递但非反对称关系
   3. norm_one       (AxiomC)   —— 构造振幅模不为 1 的函数
   4. amplitude_injective (AxiomC)  —— 构造满足 norm_one 和 comp_rule
                                    但非单射的振幅函数

🔬 新发现：已证明为冗余的公理
   1. AxiomD (op_weaving)：**从 AxiomA 逻辑推出**（因此不独立）
      —— 证明：由 input_must_be_empty 定理，
         AxiomD 的前提 |input β| = |input α| + 1 恒为 0 = 1，即 False，
         因此蕴涵式自动成立
   2. AxiomB.weaving_axiom：**从 AxiomA 逻辑推出**（因此不独立）
      —— 证明：由 input_must_be_empty 定理，
         前提 x ∈ input α 化简为 x ∈ []，即 False，
         因此蕴涵式自动成立

⚠️ 剩余未证明的独立性问题（以 Prop 形式陈述）：
   1. AxiomF 的 scale_pos/scale_limit 是否独立于 AxiomA+B+C？
   2. AxiomG/AxiomH/AxiomI 的各字段独立性？

================================================================================
-/

import Core.Axioms
import Core.Theorems
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic

namespace CSQIT.Independence

open CSQIT

section IndependenceProofs
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ============================================================================
   §1 独立性证明的方法论：如何证明"某公理独立于其他公理"
   ============================================================================

   设 S 为一组公理，A ∈ S。证明 "A 独立于 S \ {A}" 的标准方法：

     ┌──────────────────────────────────────────────────┐
     │  存在某个数学结构 M                              │
     │  M ⊧ (S \ {A})         (M 满足其他所有公理)      │
     │  M ⊭ A                 (M 不满足 A)              │
     └──────────────────────────────────────────────────┘

   这等价于：A 不能被其他公理逻辑推出（否则在满足其他公理的
   任何模型中，A 也自动成立）。

   在本文件中，我们对不同的公理选择不同的"反模型"：
     • 对 compose_assoc       —— 用 C = ℕ，compose x y := x + 2*y
     • 对 le_antisymm         —— 用 M = Bool，le := 恒真关系
     • 对 norm_one            —— 用 amplitude _ := 2 : ℂ
     • 对 amplitude_injective —— 用 amplitude _ := 1 : ℂ，C 有两元素
     • 对 AxiomD              —— 未完成

   注意：每个反模型只需要满足"同一公理的其他字段"+ 违反目标字段；
   不需要同时满足跨公理的所有字段（例如证明 compose_assoc 独立
   时不需要考虑 AxiomB）。
   ============================================================================ -/

/-! ============================================================================
   §2 AxiomA 的 compose_assoc 独立性
   ============================================================================

   目标：证明 compose_assoc 独立于 AxiomA 的其他字段。
   即构造：
     • 类型 M, C
     • input : C → List M
     • output : C → M
     • compose : C → C → C
   使得：
     (1) input_nodup       : ∀ α, (input α).Nodup
     (2) compose_input     : ∀ α β, input(compose α β) = input α ++ input β
     (3) compose_output    : ∀ α β, output(compose α β) = output β
     (4) ¬ compose_assoc   : ∃ α β γ, compose(compose α β) γ ≠ compose α (compose β γ)

   构造思路（最简反模型）：
     • 取 M := Unit     (任何类型都可以，因为 input 恒为空列表)
     • 取 C := ℕ        (自然数，提供多个元素便于写出非结合运算)
     • input α := []    (空列表，因此 input_nodup 和 compose_input 平凡成立)
     • output α := ()   (恒为 Unit，compose_output 平凡成立)
     • compose x y := x + 2 * y  (非结合运算)

   验证：compose(compose 1 2) 3 = compose 5 3 = 5 + 6 = 11
         compose 1 (compose 2 3) = compose 1 8 = 1 + 16 = 17
         11 ≠ 17，因此 compose_assoc 被违反。
   ============================================================================ -/

/-- **反模型 2A**：显式构造一个非结合律模型，作为 compose_assoc 独立性的见证。

选择 M = Unit, C = ℕ, input _ = [], output _ = (), compose x y = x + 2*y。
该模型满足 AxiomA 除 compose_assoc 外的所有字段，但不满足结合律。

**这证明了**：compose_assoc 独立于 AxiomA 的 input, output, input_nodup,
compose_input, compose_output 字段。
**这没有证明**：compose_assoc 独立于完整的 AxiomA + AxiomB + AxiomC + AxiomD。
要证明后者，需要构造同时满足 B、C、D 但违反 compose_assoc 的模型，
这是一个更加困难的问题（留作未来研究）。 -/
def exists_non_assoc_model : Prop :=
  ∃ (M C : Type)
    (input : C → List M)
    (output : C → M)
    (compose : C → C → C),
    (∀ α : C, (input α).Nodup) ∧
    (∀ α β : C, input (compose α β) = input α ++ input β) ∧
    (∀ α β : C, output (compose α β) = output β) ∧
    (∃ (α β γ : C), compose (compose α β) γ ≠ compose α (compose β γ))

/-- **定理 2.1**：compose_assoc 独立于 AxiomA 的其他字段。

显式构造反模型：
  M := Unit, C := ℕ
  input α := []
  output α := ()
  compose x y := x + 2 * y

逐条验证：
  (1) input_nodup    —— input α = []，空列表自动无重复
  (2) compose_input  —— input(compose α β) = [] = [] ++ [] = input α ++ input β
  (3) compose_output —— output(compose α β) = () = output β
  (4) 不结合         —— 取 α=1, β=2, γ=3：
                          (1+2*2)+2*3 = 11 ≠ 1+2*(2+2*3) = 17 -/
theorem compose_assoc_is_independent : exists_non_assoc_model := by
  refine' ⟨Unit, ℕ,
    fun (_ : ℕ) => ([] : List Unit),
    fun (_ : ℕ) => (),
    fun (x y : ℕ) => x + 2 * y,
    _⟩
  constructor
  · -- (1) input_nodup
    intro α
    simp [List.Nodup]
  · constructor
    · -- (2) compose_input
      intro α β
      rfl
    · constructor
      · -- (3) compose_output
        intro α β
        rfl
      · -- (4) 不满足结合律
        refine' ⟨1, 2, 3, _⟩
        decide

/-! ============================================================================
   §3 AxiomB 的 le_antisymm 独立性
   ============================================================================

   目标：证明 le_antisymm 独立于 AxiomB 的其他字段。
   即构造：
     • 类型 M, C
     • input : C → List M, output : C → M, compose : C → C → C
       （满足 AxiomA 的所有字段，AxiomB 依赖于它们）
     • le : M → M → Prop
     • lt : M → M → Prop
   使得：
     (1) le_refl                  : ∀ x, le x x
     (2) le_trans                 : ∀ x y z, le x y → le y z → le x z
     (3) lt_iff_le_not_le         : ∀ x y, lt x y ↔ (le x y ∧ ¬ le y x)
     (4) localFinite_past         : ∀ x, Set.Finite {y | lt y x}
     (5) localFinite_future       : ∀ x, Set.Finite {y | lt x y}
     (6) weaving_axiom            : ∀ α x, x ∈ input α → lt x (output α)
     (7) ¬ le_antisymm            : ∃ x y, le x y ∧ le y x ∧ x ≠ y

   构造思路（最简反模型）：
     • M := Bool (两个元素，使得可以有 x ≠ y)
     • C := Unit (任意，input 取空列表以便 weaving_axiom 空真成立)
     • input _ := [], output _ := false, compose _ _ := ()
     • le _ _ := True (恒真关系：所有元都"不晚于"所有其他元)
     • lt _ _ := False (严格序恒假，以便 lt_iff_le_not_le 成立)

   关键观察：
     le_refl, le_trans, (le x y ∧ ¬ le y x) ↔ lt x y 都成立
     （因为 le 恒真，lt 恒假，右边等价于 False，左边 le x y ∧ ¬ le y x
      即 True ∧ False = False）
     localFinite_past/future 成立（空集有限）
     weaving_axiom 成立（input _ = []，前提恒假）
     ¬ le_antisymm：取 x := false, y := true，
       则 le false true ∧ le true false 但 false ≠ true。
   ============================================================================ -/

/-- **反模型 3B**：显式构造违反 le_antisymm 的因果序模型。

选择 M = Bool, C = Unit, le _ _ = True, lt _ _ = False,
input _ = [], output _ = false, compose _ _ = ()。

**这证明了**：le_antisymm 独立于 AxiomB 的其他字段（le_refl, le_trans,
lt_iff_le_not_le, localFinite_past, localFinite_future, weaving_axiom）。
**这没有证明**：le_antisymm 在添加 AxiomA + AxiomC + AxiomD 的完整
背景下仍然独立。 -/
def exists_non_antisymm_model : Prop :=
  ∃ (M C : Type)
    (input : C → List M)
    (output : C → M)
    (compose : C → C → C)
    (le : M → M → Prop)
    (lt : M → M → Prop),
    (∀ α : C, (input α).Nodup) ∧
    (∀ α β : C, input (compose α β) = input α ++ input β) ∧
    (∀ α β : C, output (compose α β) = output β) ∧
    (∀ α β γ : C, compose (compose α β) γ = compose α (compose β γ)) ∧
    (∀ x : M, le x x) ∧
    (∀ x y z : M, le x y → le y z → le x z) ∧
    (∀ x y : M, lt x y ↔ (le x y ∧ ¬ le y x)) ∧
    (∀ x : M, Set.Finite {y : M | lt y x}) ∧
    (∀ x : M, Set.Finite {y : M | lt x y}) ∧
    (∀ (α : C) (x : M), x ∈ input α → lt x (output α)) ∧
    (∃ (x y : M), le x y ∧ le y x ∧ x ≠ y)

/-- **定理 3.1**：le_antisymm 独立于 AxiomB 的其他字段。

显式构造反模型：
  M := Bool, C := Unit
  input _ := []
  output _ := false
  compose _ _ := ()
  le _ _ := True
  lt _ _ := False

取 x := false, y := true，则 le false true ∧ le true false 但 false ≠ true。
因此 le_antisymm 不成立。 -/
theorem le_antisymm_is_independent : exists_non_antisymm_model := by
  refine' ⟨Bool, Unit,
    fun (_ : Unit) => ([] : List Bool),
    fun (_ : Unit) => false,
    fun (_ _ : Unit) => (),
    fun (_ _ : Bool) => True,
    fun (_ _ : Bool) => False,
    _⟩
  constructor
  · -- (1) input_nodup
    intro α
    cases α <;> simp [List.Nodup]
  · constructor
    · -- (2) compose_input
      intro α β
      cases α <;> cases β <;> rfl
    · constructor
      · -- (3) compose_output
        intro α β
        cases α <;> cases β <;> rfl
      · constructor
        · -- (4) compose_assoc
          intro α β γ
          cases α <;> cases β <;> cases γ <;> rfl
        · constructor
          · -- (5) le_refl
            intro x
            cases x <;> trivial
          · constructor
            · -- (6) le_trans
              intro x y z hxy hyz
              cases x <;> cases y <;> cases z <;> trivial
            · constructor
              · -- (7) lt_iff_le_not_le
                intro x y
                cases x <;> cases y <;> simp <;> tauto
              · constructor
                · -- (8) localFinite_past
                  intro x
                  cases x <;> simp <;> exact Set.finite_empty
                · constructor
                  · -- (9) localFinite_future
                    intro x
                    cases x <;> simp <;> exact Set.finite_empty
                  · constructor
                    · -- (10) weaving_axiom
                      intro α x hx
                      cases α
                      simp at hx <;> tauto
                    · -- (11) ¬ le_antisymm
                      refine' ⟨false, true, _⟩
                      constructor
                      · trivial
                      · constructor
                        · trivial
                        · decide

/-! ============================================================================
   §4 AxiomC 的 norm_one 独立性
   ============================================================================

   目标：证明 norm_one 独立于 AxiomC 的其他字段。
   即构造：
     • 类型 M, C
     • input : C → List M, output : C → M, compose : C → C → C
       （满足 AxiomA 的所有字段）
     • amplitude : C → ℂ
   使得：
     (1) comp_rule           : ∀ α β, amplitude(compose α β) = amplitude α * amplitude β
     (2) amplitude_injective : Function.Injective amplitude
     (3) ¬ norm_one          : ∃ α, Complex.normSq (amplitude α) ≠ 1

   构造思路（最简反模型）：
     • M := Unit (任意)
     • C := ℕ (多个元素以便振幅可区分)
     • input _ := [], output _ := (), compose x y := x + y
       (整数加法，满足结合律 —— 由 AxiomA 要求)
     • amplitude n := (2 : ℂ) ^ n     (2 的 n 次幂)
       —— amplitude_injective 成立（2 ≠ 0，2^n 可区分）
       —— comp_rule 成立：2^(x+y) = 2^x * 2^y
       — ——norm_one 不成立：取 n = 0，|2^0|² = 1，但取 n = 1，|2^1|² = 4 ≠ 1
       —— norm_one 不成立

   其实更简单：取 C = Unit, amplitude _ = 2
   — 则 norm_one 不成立，但 comp_rule 和 amplitude_injective 成立
   （只有一个元素，所以 comp_rule 与 injectivity 都是平凡的）。

   最简方案：C = Unit, amplitude _ = 2,
     norm_one 被违反（|2|² = 4 ≠ 1），
     comp_rule 成立（2 = 2 * 2 吗？不，2 ≠ 4）。
   哦！这里有问题。需要：amplitude(compose (), ()) = amplitude () * amplitude ()
   即 2 = 2 * 2 = 4：错误！
   所以 comp_rule 也被违反了。
   所以这个简单模型不行。

   修改方案：取 compose _ _ := ()，并取 amplitude _ = 1
   —— 但这样 norm_one 反而成立了。

   实际上：如果 C 只有一个元素，那么 compose _ _ = ()，
   comp_rule 给出 amplitude () = amplitude () * amplitude ()，
   即 z = z * z，从而 z = 0 或 z = 1。
   —— 如果 z = 0，则 |0|² = 0 ≠ 1，norm_one 不成立；
       但是否满足 comp_rule 和 amplitude_injective？
       - comp_rule: 0 = 0 * 0 ✓
       - amplitude_injective：只有一个元素，成立 ✓
       - norm_one：|0|² = 0 ≠ 1 ✗ ✓
       好，那么 z = 0 满足！

   等等，amplitude_injective 呢？Function.Injective 要求：
     amplitude x = amplitude y → x = y
   在 C = Unit 时，这是 vacuously true（只有一个元素）。

   好的，我们用 C = Unit, amplitude _ = 0。

   再想想，norm_one 的定义是 Complex.normSq (amplitude α) = 1，
   所以如果 amplitude α = 0，那么 |0|² = 0 ≠ 1，违反 norm_one。
   comp_rule：0 = 0 * 0，成立。
   amplitude_injective：在 Unit 上平凡成立。

   完美！但等等，这是否真的满足 amplitude_injective？
   是的，因为 Function.Injective amplitude 的定义是：
     ∀ x y : Unit, amplitude x = amplitude y → x = y
   x 和 y 必然都是 ()，所以结论成立。
   但是，我们是否需要 norm_one 在 *所有*规则上成立？是的，norm_one 要求
   ∀ α, Complex.normSq (amplitude α) = 1。取 α = ()，有 |0|² = 0 ≠ 1，
   所以 norm_one 被违反。✓

   但是，我们是否真的构造了一个反模型来证明 norm_one 的独立性？
   让我们重新审视。我们需要的是：
   (1) comp_rule 成立
   (2) amplitude_injective 成立
   (3) norm_one 不成立

   用 C = Unit, amplitude _ = 0：
   - comp_rule: 0 = 0 * 0 ✓
   - amplitude_injective：vacuous ✓
   - norm_one: |0|² = 0 ≠ 1，即 ∃ α, Complex.normSq (amplitude α) ≠ 1，✓
   好。

   等等，还有一个问题：AxiomC 的定义要求 AxiomA 的背景。
   所以我们还需要给出 input, output, compose 以及满足所有 AxiomA 字段。
   简单：取 input _ = [], output _ = (), compose _ _ = ()，
   那么 input_nodup, compose_input, compose_output, compose_assoc 都成立。
   完美。

   —— 但是否 amplitude_injective 是真正我们需要的？让我们回顾
   原始 AxiomC：它是一个 class，要求 amplitude_injective。
   —— 在当前反模型中，amplitude_injective 成立，是的。
   —— 我们可以进一步放宽：实际上，我们只需要证明 norm_one 独立于
      comp_rule，甚至不需要 amplitude_injective。但为了更加严谨
      （证明 norm_one 独立于 comp_rule + amplitude_injective），
      我们包含 amplitude_injective。

   最后，为了使证明更有意思（反模型不太平凡），我们也可以选择 C = Bool
   并构造 amplitude true = 1, amplitude false = 2。
   —— comp_rule 要求 amplitude(compose α β) = amplitude α * amplitude β
   —— 这意味着我们需要定义 compose 来满足这个乘法等式。
   —— 我们可以让 compose 是 "加法"：定义 compose 在某种意义上对应乘积。
   —— 但 Bool 上天然没有这种结构。所以最简单的是用单元素模型。
   —— 实际上，让我们再次使用 C = Unit, amplitude _ = 0。
   —— 这虽然非常简单，但是严格证明了独立性。
   ============================================================================ -/

/-- **反模型 4C-norm_one**：显式构造违反 norm_one 的振幅模型。

选择 M = Unit, C = Unit, amplitude _ = 0。
该模型满足 comp_rule 和 amplitude_injective，但不满足 norm_one。

**这证明了**：norm_one 独立于 AxiomC 的其他字段（comp_rule, amplitude_injective）。
**这没有证明**：norm_one 独立于 AxiomA + AxiomB + AxiomC + AxiomD 中除 norm_one 外的全部公理。 -/
def exists_non_norm_one_model : Prop :=
  ∃ (M C : Type)
    (input : C → List M)
    (output : C → M)
    (compose : C → C → C)
    (amplitude : C → ℂ),
    (∀ α : C, (input α).Nodup) ∧
    (∀ α β : C, input (compose α β) = input α ++ input β) ∧
    (∀ α β : C, output (compose α β) = output β) ∧
    (∀ α β γ : C, compose (compose α β) γ = compose α (compose β γ)) ∧
    (∀ α β : C, amplitude (compose α β) = amplitude α * amplitude β) ∧
    Function.Injective amplitude ∧
    (∃ (α : C), Complex.normSq (amplitude α) ≠ 1)

/-- **定理 4.1**：norm_one 独立于 AxiomC 的其他字段。

显式构造反模型：
  M := Unit, C := Unit
  input _ := []
  output _ := ()
  compose _ _ := ()
  amplitude _ := 0

验证：
  - AxiomA 各字段：平凡成立
  - comp_rule: 0 = 0 * 0，成立
  - amplitude_injective: 单元素类型上平凡成立
  - norm_one: |0|² = 0 ≠ 1，不成立 ✓ -/
theorem norm_one_is_independent : exists_non_norm_one_model := by
  refine' ⟨Unit, Unit,
    fun (_ : Unit) => ([] : List Unit),
    fun (_ : Unit) => (),
    fun (_ _ : Unit) => (),
    fun (_ : Unit) => (0 : ℂ),
    _⟩
  constructor
  · -- input_nodup
    intro α
    cases α <;> simp [List.Nodup]
  · constructor
    · -- compose_input
      intro α β
      cases α <;> cases β <;> rfl
    · constructor
      · -- compose_output
        intro α β
        cases α <;> cases β <;> rfl
      · constructor
        · -- compose_assoc
          intro α β γ
          cases α <;> cases β <;> cases γ <;> rfl
        · constructor
          · -- comp_rule
            intro α β
            cases α <;> cases β <;> simp <;> norm_num
          · constructor
            · -- amplitude_injective
              intro x y h
              cases x <;> cases y <;> rfl
            · -- ¬ norm_one
              refine' ⟨(), _⟩
              simp [Complex.normSq]
              <;> norm_num

/-! ============================================================================
   §5 AxiomC 的 amplitude_injective 独立性
   ============================================================================

   目标：证明 amplitude_injective 独立于 AxiomC 的其他字段。
   即构造：
     • 类型 M, C（|C| ≥ 2，便于 amplitude_injective 被违反）
     • input/output/compose（满足 AxiomA）
     • amplitude : C → ℂ
   使得：
     (1) norm_one       : ∀ α, Complex.normSq (amplitude α) = 1
     (2) comp_rule      : ∀ α β, amplitude(compose α β) = amplitude α * amplitude β
     (3) ¬ injective    : ∃ α β, α ≠ β ∧ amplitude α = amplitude β

   构造思路：
     • M := Unit
     • C := Bool (有两个元素，false 和 true)
     • input _ := []
     • output _ := ()
     • compose _ _ := false     (组合结果恒为 false)
     • amplitude _ := 1         (所有规则的振幅都为 1)

   验证：
     (1) norm_one    : Complex.normSq 1 = 1，成立
     (2) comp_rule   : 1 = 1 * 1，成立
     (3) ¬ injective : amplitude false = amplitude true = 1，false ≠ true

   更有意思的可选方案：
     C := {r₁, r₂, ..., rₙ}, amplitude(rᵢ) := 1，compose 为任意恒等组合。
     这也满足 norm_one 和 comp_rule，但 amplitude_injective 不成立。
   ============================================================================ -/

/-- **反模型 5C-injective**：显式构造违反 amplitude_injective 的振幅模型。

选择 M = Unit, C = Bool, input _ = [], output _ = (), compose _ _ = false,
amplitude _ = 1。

**这证明了**：amplitude_injective 独立于 AxiomC 的其他字段（norm_one, comp_rule）。
**这没有证明**：amplitude_injective 在完整 CSQIT 理论中的独立性。 -/
def exists_non_injective_model : Prop :=
  ∃ (M C : Type)
    (input : C → List M)
    (output : C → M)
    (compose : C → C → C)
    (amplitude : C → ℂ),
    (∀ α : C, (input α).Nodup) ∧
    (∀ α β : C, input (compose α β) = input α ++ input β) ∧
    (∀ α β : C, output (compose α β) = output β) ∧
    (∀ α β γ : C, compose (compose α β) γ = compose α (compose β γ)) ∧
    (∀ α : C, Complex.normSq (amplitude α) = 1) ∧
    (∀ α β : C, amplitude (compose α β) = amplitude α * amplitude β) ∧
    (∃ (α β : C), α ≠ β ∧ amplitude α = amplitude β)

/-- **定理 5.1**：amplitude_injective 独立于 AxiomC 的其他字段。

显式构造反模型：
  M := Unit, C := Bool
  input _ := []
  output _ := ()
  compose _ _ := false
  amplitude _ := 1

验证：
  - norm_one:     |1|² = 1 ✓
  - comp_rule:    1 = 1 * 1 ✓
  - ¬ injective:  amplitude false = amplitude true = 1, false ≠ true ✓ -/
theorem amplitude_injective_is_independent : exists_non_injective_model := by
  refine' ⟨Unit, Bool,
    fun (_ : Bool) => ([] : List Unit),
    fun (_ : Bool) => (),
    fun (_ _ : Bool) => false,
    fun (_ : Bool) => (1 : ℂ),
    _⟩
  constructor
  · -- input_nodup
    intro α
    cases α <;> simp [List.Nodup]
  · constructor
    · -- compose_input
      intro α β
      cases α <;> cases β <;> rfl
    · constructor
      · -- compose_output
        intro α β
        cases α <;> cases β <;> rfl
      · constructor
        · -- compose_assoc
          intro α β γ
          cases α <;> cases β <;> cases γ <;> rfl
        · constructor
          · -- norm_one
            intro α
            cases α <;> simp [Complex.normSq] <;> norm_num
          · constructor
            · -- comp_rule
              intro α β
              cases α <;> cases β <;> simp <;> norm_num
            · -- ¬ amplitude_injective
              refine' ⟨false, true, _⟩
              constructor
              · decide
              · rfl

/-! ============================================================================
   §6 AxiomD 的独立性分析（开放问题）
   ============================================================================

   核心问题：AxiomD (op_weaving) 是否独立于 AxiomA + AxiomB + AxiomC？

   要证明这一点，需要构造一个模型满足：
     (1) AxiomA 的所有字段（input, output, compose, compose_input,
         compose_output, compose_assoc）
     (2) AxiomB 的所有字段（le, lt, le_refl, le_trans, le_antisymm,
         lt_iff_le_not_le, localFinite_past/future, weaving_axiom）
     (3) AxiomC 的所有字段（norm_one, comp_rule, amplitude_injective）
     (4) 不满足 AxiomD.op_weaving：
         存在 α, β : C 使得：
           (a) B.lt (A.output α) (A.output β)
           (b) (A.input β).length = (A.input α).length + 1
           (c) ¬ ∃ γ : C, A.compose α γ = β

   主要障碍：

   障碍 1：AxiomA.compose_input 的强约束
     compose_input 要求 input(compose α β) = input α ++ input β。
     这意味着 |input(compose α β)| = |input α| + |input β|。
     如果 C 只有一个元素（|C| = 1），设 c 为唯一元素，则
     compose c c = c，于是 input c = input c ++ input c，
     由 List 性质推出 input c = []。
     因此单规则模型中 input 必为空。

   障碍 2：weaving_axiom 的约束
     weaving_axiom 要求 ∀ α x, x ∈ input α → B.lt x (A.output α)。
     如果 input α = []，则前提恒假，weaving_axiom 空真成立。
     但此时也没有任何关系元被"编织"，B.lt 的行为不受 weaving_axiom 约束。

   障碍 3：要违反 op_weaving，必须存在 "输出上有严格序" 的规则对
     需要存在 α, β 使得 B.lt (A.output α) (A.output β)。
     这要求 output 不是常函数，即至少有两个不同的 output 值。
     同时，我们需要 (A.input β).length = (A.input α).length + 1。
     在 |C| = 1 时，必然 input α = []（见障碍 1），所以
     (A.input α).length = 0，(A.input β).length = 0，而 0 = 0 + 1 即 0 = 1，矛盾。
     因此在单规则模型中 op_weaving 的前提恒假，AxiomD 空真成立。
     —— 要构造违反 op_weaving 的模型，必须 |C| ≥ 2。

   障碍 4：|C| ≥ 2 时的一致性问题
     一旦 |C| ≥ 2，compose_input 就变得高度制约：
     —— 每个规则 α 都有一个 input 列表长度 n_α；
     —— 组合的 input 长度 = n_α + n_β；
     —— 但同时 compose 的 output 必须等于 output β；
     —— 这与 amplitude_injective 和 comp_rule 一起构成复杂约束。

   开放问题：是否存在这样的模型？

   当前思路：或许可以让一些规则有非空 input，另一些规则有空 input，
   使得存在 α 满足 |input α| = k 且 output α = x，同时存在 β 满足
   |input β| = k + 1 且 output β = y （y 是 x 的"严格后继"），
   但不存在 γ 使得 compose α γ = β。
   由于 amplitude_injective 和 comp_rule 要求振幅函数是单射群同态，
   这对 C 施加了"至少有一个非平凡自由群结构"的约束——
   当 |C| = 2 时 C 是 Bool，compose 在 Bool 上的行为被 comp_rule 制约。
   这是尚未解决的技术困难。

   注：以下将 "AxiomD 独立于 AxiomA + AxiomB + AxiomC" 陈述为
   一个未证明的 Prop 命题（而非已证明的定理），以避免使用 sorry。
   ============================================================================ -/

/-! ----------------------------------------------------------------------------
   6.1 新发现：AxiomD 实际上是 AxiomA 的逻辑推论（因此不独立）

   由 Core/Theorems.lean 中的 input_must_be_empty 定理：
   在任何满足 AxiomA 的模型中，对所有 α : C，都有 input α = []。

   因此：
   (1) |input β| = 0，|input α| = 0
   (2) AxiomD 的前提 |input β| = |input α| + 1 即 0 = 0 + 1，即 False
   (3) False → P 对任何 P 都成立（ex falso quodlibet）
   (4) 因此 AxiomD.op_weaving 自动成立

   结论：AxiomD 不独立于 AxiomA——它是 AxiomA 的逻辑推论。
   ---------------------------------------------------------------------------- -/

/-- **定理 6.1**：在任何满足 AxiomA 的模型中，AxiomD.op_weaving 的前提恒为 False。

证明：由 input_must_be_empty 定理，对所有 α β，都有
input α = [] 且 input β = []，因此 (input β).length = 0 且 (input α).length = 0。
前提 (input β).length = (input α).length + 1 即 0 = 0 + 1，即 0 = 1，矛盾。
因此前提恒为 False。 -/
theorem axiomD_premise_always_false {M C : Type*} [A : AxiomA M C]
    (α β : C) : ¬ ((A.input β).length = (A.input α).length + 1) := by
  have hα : A.input α = [] := input_must_be_empty α
  have hβ : A.input β = [] := input_must_be_empty β
  rw [hα, hβ]
  <;> simp
  <;> omega

/-- **定理 6.2**：在任何满足 AxiomA + AxiomB + AxiomC 的模型中，AxiomD 自动成立。

这意味着 AxiomD **不独立于** AxiomA + AxiomB + AxiomC——它实际上是冗余的。

证明思路：AxiomD 形如 "前提 → 结论"，而我们已证明前提恒为 False，
因此 False → 结论 自动成立。 -/
theorem axiomD_is_redundant {M C : Type*} [A : AxiomA M C] [B : AxiomB M C] [Cx : AxiomC M C] :
    ∀ (α β : C), B.lt (A.output α) (A.output β) →
      (A.input β).length = (A.input α).length + 1 →
      ∃ (γ : C), A.compose α γ = β := by
  intro α β h1 h2
  exfalso
  exact axiomD_premise_always_false α β h2

/-- **定理 6.3**：AxiomB.weaving_axiom 也是 AxiomA 的逻辑推论。

证明：前提 x ∈ A.input α，由 input_must_be_empty，A.input α = []，
所以前提即 x ∈ []，即 False，因此蕴涵式自动成立。 -/
theorem weaving_axiom_is_redundant {M C : Type*} [A : AxiomA M C] [B : AxiomB M C] :
    ∀ (α : C) (x : M), x ∈ A.input α → B.lt x (A.output α) := by
  intro α x h
  have h1 : A.input α = [] := input_must_be_empty α
  rw [h1] at h
  <;> simp at h <;> tauto

/-! ----------------------------------------------------------------------------
   6.2 理论上的兴趣：虽然 AxiomD 被证明是冗余的，
       但以下 Prop 陈述仍然保留，作为"如果有人想在不使用 input_must_be_empty
       定理的情况下独立研究"的框架。
       实际结论由上面的定理 6.1-6.3 给出。
   ---------------------------------------------------------------------------- -/

/-- **开放问题 6D**：AxiomD (op_weaving) 是否独立于 AxiomA + AxiomB + AxiomC？

这是本文件中**尚未完成**的独立性研究。

**状态**：⚠️ 未证明。目前只知道：
  • 在退化单规则模型 (C = Unit, input = []) 中 AxiomD 空真成立；
  • 非平凡多规则模型 (|C| ≥ 2, ∃ α, input α ≠ []) 的存在性本身就是
    一个开放问题（见 Consistency.lean）；
  • 构造多规则模型的主要障碍是 AxiomA.compose_input 对 input 长度
    施加的强约束：若 |C| = 2，compose 需要同时满足结合律、输入拼接
    一致性、以及 amplitude_injective+comp_rule 的复振幅约束。

**证明方向（如果尝试证明）**：构造一个具有 |C| ≥ 2 的模型，
其中存在规则 α, β 使得 B.lt (A.output α) (A.output β) 且
(A.input β).length = (A.input α).length + 1，但不存在 γ 使得
A.compose α γ = β。
此构造尚需新的组合设计，留作未来研究。 -/
def axiomD_independent_of_ABC : Prop :=
  ∃ (M C : Type)
    (instA : AxiomA M C)
    (instB : AxiomB M C)
    (_ : AxiomC M C),
    ∃ (α β : C),
      (instB.lt (instA.output α) (instA.output β)) ∧
      ((instA.input β).length = (instA.input α).length + 1) ∧
      (¬ ∃ (γ : C), instA.compose α γ = β)

/-! ============================================================================
   §7 总结：CSQIT 公理的独立性图
   ============================================================================

   综合 §2-§6 的结果，我们得到以下严格证明的结论：

   ┌─────────────────────────────────────────────────────────┐
   │ 已证明：                                                  │
   │                                                           │
   │  1. compose_assoc         ⊥ {AxiomA \ {compose_assoc}}     │
   │     (定理 2.1)                                           │
   │                                                           │
   │  2. le_antisymm           ⊥ {AxiomB \ {le_antisymm}}       │
   │     (定理 3.1)                                           │
   │                                                           │
   │  3. norm_one              ⊥ {comp_rule, amplitude_injective}
   │     (定理 4.1)                                           │
   │                                                           │
   │  4. amplitude_injective   ⊥ {norm_one, comp_rule}          │
   │     (定理 5.1)                                           │
   │                                                           │
   │ 🔬 已证明为冗余：                                          │
   │  5. AxiomD(op_weaving) ⇒ 由 AxiomA 推出（冗余，不独立）       │
   │     (定理 6.2)                                           │
   │                                                           │
   │  6. AxiomB.weaving_axiom ⇒ 由 AxiomA 推出（冗余，不独立）   │
   │     (定理 6.3)                                           │
   └─────────────────────────────────────────────────────────┘

   其中"X ⊥ S"读作"X 独立于集合 S"，即存在模型满足 S 但不满足 X。

   注意：以上的独立性都是"同一公理内部字段"的独立性，
   而非"跨公理独立性"。跨公理独立性（例如 "AxiomA 独立于
   AxiomB + AxiomC + AxiomD"）是更强的结论，需要更复杂的
   模型构造。

   🔬 关键新发现（补充）：
   本文件最初提出 AxiomD 的独立性作为开放问题。
   基于 Core/Theorems.lean 中的 input_must_be_empty 定理，
   现在我们知道：AxiomD 和 weaving_axiom 实际上都是 AxiomA 的逻辑推论。
   这意味着它们在 CSQIT 公理体系中是**冗余的**，而非独立的。

   这是一个重要的澄清：
   - 不能用"反模型"方法来证明 AxiomD 的独立性
   - 因为任何满足 AxiomA 的模型都自动满足 AxiomD
   - AxiomD 唯一可能"被违反"的方式是在不满足 AxiomA 的模型中
     （但这样的模型已经不属于 CSQIT 的标准模型了）
   ============================================================================ -/

/-- **总结定理**：CSQIT 核心公理中至少有四个字段被证明是独立的。

这个总结把 §2-§5 的四个结论组合成一个存在性陈述：

  1. 存在不满足结合律但满足其他 AxiomA 字段的结构
  2. 存在不满足反对称性但满足其他 AxiomB 字段的结构
  3. 存在不满足 norm_one 但满足其他 AxiomC 字段的结构
  4. 存在不满足 amplitude_injective 但满足其他 AxiomC 字段的结构

注意：这四个是**不同**的模型（每个专门设计来违反一个特定字段），
不是同一个模型同时违反所有四个字段。 -/
theorem csqit_has_four_independent_fields :
  exists_non_assoc_model ∧
  exists_non_antisymm_model ∧
  exists_non_norm_one_model ∧
  exists_non_injective_model := by
  constructor
  · exact compose_assoc_is_independent
  · constructor
    · exact le_antisymm_is_independent
    · constructor
      · exact norm_one_is_independent
      · exact amplitude_injective_is_independent

/-! ============================================================================
   本文件的最终状态（诚实评估）
   ============================================================================

   已严格证明的结论（✅ 完整、可机器检查的证明）：
   1. compose_assoc 独立于 AxiomA 的其他字段（定理 2.1）
   2. le_antisymm 独立于 AxiomB 的其他字段（定理 3.1）
   3. norm_one 独立于 AxiomC 的 comp_rule + amplitude_injective 字段
      （定理 4.1）
   4. amplitude_injective 独立于 AxiomC 的 norm_one + comp_rule 字段
      （定理 5.1）
   5. 综合存在性陈述：csqit_has_four_independent_fields（定理 7.1）

   未证明 / 开放问题（⚠️ 以 Prop 形式陈述，未断言已证明）：
   1. axiomD_independent_of_ABC —— AxiomD 是否独立于 AxiomA + AxiomB + AxiomC？
      主要障碍：AxiomA.compose_input 对多规则模型施加的强约束，
      结合 amplitude_injective + comp_rule 的复振幅约束，
      使非平凡反模型构造极具挑战。

   与 Consistency.lean 的关系：
   — Consistency.lean 关注公理的**相容性**（是否有模型满足所有公理）
   — Independence.lean 关注公理的**独立性**（是否有模型恰好违反一个公理）
   — 两者互补：相容性证明"公理之间不互相矛盾"，
     独立性证明"公理之间不互相蕴涵"。
   ============================================================================ -/

end IndependenceProofs

end CSQIT.Independence
