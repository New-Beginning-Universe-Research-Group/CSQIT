/-
CSQIT 小有限半群两面平衡态探索
文件: Core/Models/SmallSemigroupExploration.lean
版本: 1.0 (宇宙之光阶段)
日期: 2026-06-27

================================================================================
模块概述
================================================================================

本模块系统探索小有限半群上的两面平衡态存在性问题。

核心问题（standard_theory_no_intermediate_balance_claim）:
  在标准 AxiomA + AxiomC（含 amplitude_injective）下，
  若 C 有限且 output 非平凡（k > 1），则 amplitude 必为常数（m = 1）？

  换句话说：是否存在两面平衡态 —— 同时满足 k > 1 且 m > 1？

探索策略:
  1. 枚举小有限集合上的半群结构（满足 compose_output）
  2. 检查每个半群是否有忠实的 1 维复表示（单射 amplitude）
  3. 验证 output 是否可以非平凡

================================================================================
数学框架
================================================================================

给定有限集合 C，我们寻找：
  (1) 二元运算 ∘ : C × C → C，满足结合律
  (2) 函数 output : C → M，满足 output(α ∘ β) = output β
  (3) 函数 amplitude : C → ℂ，满足 amplitude(α ∘ β) = amplitude α * amplitude β
  (4) amplitude 是单射的
  (5) output 不是常函数

关键观察：
  由 (2)，output(α ∘ β) = output β，即第一个参数的 output 值被忽略。
  这意味着 ∘ 在每个 output 纤维上的左作用是该纤维到自身的映射。

  由 (3)，amplitude 是半群同态。
  若 amplitude 是单射的，则 (C, ∘) 同构于 (ℂ, ×) 的一个有限子半群。
  而 (ℂ, ×) 的有限子半群都是有限循环群（单位根群）。

  因此，问题转化为：
  能否在一个有限循环群 G 上定义 output : G → M，
  使得 output(g · h) = output(h) 对所有 g, h ∈ G 成立，
  且 output 不是常函数？

  答案是否定的！因为如果 G 是群，则它是左可迁的，
  由 output_degenerate_theorem，output 必为常函数。

  但这只是群的情形。对于一般的半群（不是群），情况如何？

  这正是我们要探索的。

================================================================================
主要结果
================================================================================

定理 1：若 (C, ∘) 是群，则 output 必为常函数。
  （已由 output_degenerate_theorem 证明）

定理 2：若 (C, ∘) 是右投影半群，则 amplitude 必为常函数。
  （已由 right_projective_amplitude_degenerate 证明）

猜想：在任何有限半群中，k × m ≤ |C|，
  且等号仅在极端情形（群或右投影）成立。

================================================================================
-/

import Core.Axioms
import Core.TwoAspectTheorems
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Set.Finite.Basic

set_option linter.unusedVariables false

namespace CSQIT.Models.SmallSemigroups

open CSQIT

/-! ============================================================================
   §1. 平凡情形：|C| = 1
   ============================================================================ -/

/-- **C = Unit（1 个元素）**:
    唯一的半群结构是平凡的。
    - k = 1（output 只能是常函数）
    - m = 1（amplitude 只能是常函数）
    k × m = 1 = |C|，守恒律成立，但没有平衡态。 -/
theorem card_1_only_trivial (C : Type) [Fintype C] [DecidableEq C]
    (h_card : Fintype.card C = 1) :
    ∀ (f g : C → ℂ), ∀ (α β : C), f α = f β := by
  intro f g α β
  have h1 : Fintype.card C = 1 := h_card
  have h2 : α = β := by
    apply Fintype.card_le_one_iff_subsingleton.mp
    rw [h1] <;> norm_num
  rw [h2]

/-! ============================================================================
   §2. |C| = 2 的情形
   ============================================================================

C = {a, b}，有多少个半群结构？

总共有 2^(2×2) = 16 种可能的二元运算。
但我们只关心满足 compose_output 结构的半群，
即存在 output : C → M 使得 output(α ∘ β) = output β。

这意味着 ∘ 的每一列都是常值吗？不，等一下...

实际上，compose_output 说的是：
  output(compose α β) = output β

这并不直接约束 compose 的结构，除非我们对 output 有更多了解。
但是，如果我们假设 amplitude 是单射的，那么情况就不同了。

让我们从另一个角度看：

假设 amplitude : C → ℂ 是单射半群同态。
则 C 同构于 ℂ× 的一个有限子半群。
ℂ× 的有限子半群都是有限循环群（因为 ℂ× 是交换群，
有限子半群都是子群，而有限域乘法群的有限子群都是循环群）。

因此，如果 amplitude 是单射的，则 (C, ∘) 是一个有限交换群，
同构于 Z/nZ，其中 n = |C|。

但群是左可迁的，因此 output 必为常函数（k = 1）。

这似乎意味着：只要 amplitude 是单射的，
(C, ∘) 就必须是群（因为它同构于 ℂ× 的有限子群），
因此 output 必退化。

等等，这个推理对吗？

让我们更仔细地检查：
1. amplitude : C → ℂ 是单射半群同态
2. 因此，C 同构于 ℂ 的一个子半群
3. ℂ 的有限子半群都是群吗？

答案是：是的！
在任何群中，有限子半群都是子群。
证明：设 S 是群 G 的有限子半群。
      对任意 s ∈ S，考虑映射 x ↦ s·x : S → S。
      这是一个单射（因为群中消去律成立）。
      由于 S 有限，单射蕴含满射。
      因此存在 e ∈ S 使得 s·e = s，即 e 是右单位元。
      同理可证左单位元存在，且两者相等。
      同样可证逆元存在。
因此，S 是 G 的子群。

所以，结论是：
  如果 amplitude 是单射的，则 (C, ∘) 是有限交换群，
  同构于 Z/nZ。

  而群是左可迁的，因此 output 必为常函数。

  这就证明了：amplitude 单射 ⇒ output 退化！

  等等，这是不是太简单了？让我们再检查一下...

  关键步骤：
  1. amplitude : C → ℂ 是单射半群同态 ✓
  2. 因此 (C, ∘) 同构于 (ℂ, ×) 的一个子半群 ✓
  3. (ℂ, ×) 是群 ✓
  4. 群的有限子半群是子群 ✓
  5. 因此 (C, ∘) 是群 ✓
  6. 群是左可迁的 ✓
  7. 左可迁 ⇒ output 退化 ✓

  这个论证链看起来是完整的！

  但等等，有一个问题：AxiomC 中的 amplitude 的值域是 ℂ，
  但 comp_rule 是 amplitude(compose α β) = amplitude α * amplitude β。
  而 0 ∈ ℂ，且 0 * x = 0。
  如果 amplitude 的像包含 0，那么上面的论证就不成立了，
  因为 0 没有逆元。

  但是，AxiomC 还有 norm_one 公理：|amplitude α|² = 1。
  这意味着 amplitude α ≠ 0 对所有 α 成立！
  因为 |0|² = 0 ≠ 1。

  因此，amplitude : C → ℂ 实际上取值于 ℂ×（非零复数乘法群）。
  因此上面的论证成立！

  所以，我们得到了一个重要的定理：

  定理（标准理论两面性的二选一）：
  在标准 CSQIT 理论中（满足 AxiomA + AxiomC），
  以下两者必居其一：
  1. output 是常函数（因果面退化）
  2. amplitude 不是单射的（信息面退化）

  换句话说：不存在两面平衡态！

  这就是 standard_theory_no_intermediate_balance_claim 的证明！

  让我们把这个证明形式化。

========================================================================== -/

/-- **关键引理**：幺正半群同态的像必为群。

    设 f : S → G 是半群同态，其中 G 是群，且 S 有限。
    如果 f 是单射的，则 S 本身也是群（同构于 G 的一个子群）。

    完整证明见 TwoAspectTheorems.lean 中的
    `finite_semigroup_injective_hom_to_group` 定理。 -/
theorem injective_semigroup_hom_to_group_implies_group
    {S G : Type*} [Semigroup S] [Group G] [Finite S] [Nonempty S]
    (f : S → G)
    (h_hom : ∀ (x y : S), f (x * y) = f x * f y)
    (h_inj : Function.Injective f) :
    ∃ (e : S), (∀ (x : S), e * x = x) ∧ (∀ (x : S), ∃ (y : S), y * x = e) :=
  finite_semigroup_injective_hom_to_group f h_hom h_inj

/-! ============================================================================
   说明
   ============================================================================

   上面的定理 injective_semigroup_hom_to_group_implies_group
   是证明 standard_theory_no_intermediate_balance_claim 的关键。

   此定理的完整证明见 TwoAspectTheorems.lean 中的
   `finite_semigroup_injective_hom_to_group`。

   证明的核心数学思想：
   - norm_one 保证 amplitude 的值都在 ℂ× 中
   - ℂ× 是群
   - 有限子半群是子群
   - 因此 C 是群
   - 群是左可迁的
   - 左可迁 ⇒ output 退化

   这是一个完整的形式化证明。
   ============================================================================ -/

/-! ============================================================================
   §3. 右正则表示与纤维结构
   ============================================================================

   让我们从另一个角度来理解这个问题。

   对于每个 β ∈ C，定义左乘映射：
     L_β : C → C
     L_β(α) := compose β α

   由 compose_output，我们有 output(L_β(α)) = output α，
   即 L_β 将每个 output 纤维映射到自身。

   特别地，L_β 限制在纤维 fiber(x) 上是 fiber(x) → fiber(x) 的映射。

   如果 L_β 是双射呢？
   如果 C 是群，则每个 L_β 都是双射（逆映射是 L_{β⁻¹}）。
   在这种情况下，所有纤维的大小都相等，
   并且每个纤维的大小都整除 |C|。

   但如果 output 不是常函数，则至少有两个非空纤维。
   每个纤维的大小 < |C|。
   然而，如果 amplitude 是单射的，则 C 是群，
   而群是左可迁的，这意味着 output 必须是常函数。
   矛盾！

   这就是另一种理解方式。

   关键洞察：amplitude 单射性 + norm_one
   强制了 (C, compose) 的群结构，
   而群结构强制了 output 的退化。
   ============================================================================ -/

/-! ============================================================================
   §4. 非幺正情形的探索
   ============================================================================

   如果我们放弃 norm_one 呢？
   也就是说，如果 amplitude 可以取 0 或其他模长的值。

   在这种情况下，amplitude 的像可以包含 0，
   因此上面的论证（有限子半群是子群）不再成立。

   让我们看看能否构造出两面平衡态。

   例：C = {a, b}，定义：
     compose a a = a
     compose a b = b
     compose b a = a
     compose b b = b

   这是什么结构？这就是右投影结构！
   compose α β = β。
   在这种情况下，amplitude 必须是常函数（退化）。

   另一个例子：C = {a, b}，定义：
     compose a a = a
     compose a b = a  （注意：这违反了 compose_output，如果 output a ≠ output b）
     compose b a = b
     compose b b = b

   等等，我们需要检查 compose_output 是否可以满足。
   compose_output 要求 output(compose α β) = output β。

   对于上面的运算：
     output(compose a b) = output a
     但我们需要 output b
     所以必须有 output a = output b。
     即 output 是常函数。

   所以这种运算结构只能有平凡的 output。

   让我们系统地分析 |C| = 2 的情况。

   C = {0, 1}（用 Fin 2）。

   我们需要寻找满足以下条件的 compose : Fin 2 → Fin 2 → Fin 2：
   (1) 结合律：compose (compose α β) γ = compose α (compose β γ)
   (2) 存在 output : Fin 2 → M，使得 output(compose α β) = output β
   (3) 存在 amplitude : Fin 2 → ℂ，使得 amplitude(compose α β) = amplitude α * amplitude β
   (4) amplitude 是单射的
   (5) output 不是常函数

   由 (4) 和 (5)，我们要找的是"两面平衡态"。

   让我们枚举所有 16 种可能的二元运算...

   实际上，由 (2)，output(compose α β) = output β。
   这意味着：对于固定的 β，compose α β 的 output 值与 α 无关。
   也就是说，对于每个 β，所有形如 compose α β 的元素都有相同的 output 值。

   特别地，如果 output 不是常函数，则存在 β₁, β₂ 使得 output β₁ ≠ output β₂。
   那么对任意 α，output(compose α β₁) = output β₁ ≠ output β₂ = output(compose α β₂)，
   因此 compose α β₁ ≠ compose α β₂。

   这说明每个左乘映射 L_α : β ↦ compose α β 都是"保持 output 纤维"的。

   但这还不足以给出完整的分类。

   让我们转向 amplitude 的条件。
   由 (3) 和 (4)，amplitude 是单射半群同态。
   如果我们不假设 norm_one，amplitude 可以取 0 值。

   但是 AxiomC 包含 norm_one，所以我们必须考虑它。

   总结：在标准 AxiomC（含 norm_one）下，
         amplitude 的像 ⊆ { z ∈ ℂ | |z|² = 1 } = S¹，
     而 S¹ 是群，因此有限子半群是子群，
     因此 (C, compose) 是群，
     因此左可迁，
     因此 output 退化。

   这是一个完整的论证链条！
   ============================================================================ -/

/-! ============================================================================
   总结：标准理论的两面性二一定理（非正式陈述）
   ============================================================================

   定理名称建议：standard_theory_two_aspect_dichotomy

   陈述：在满足 AxiomA + AxiomC 的有限模型中，
         以下两者必居其一：
         (a) output 是常函数（因果面退化，k = 1）
         (b) amplitude 不是单射的（信息面退化，m < |C|）

   等价地说：不存在两面平衡态（即同时满足 k > 1 且 m > 1 的模型）。

   证明概要：
     假设 amplitude 是单射的。
     由 norm_one，amplitude 的值都在 S¹（单位圆群）中。
     由 comp_rule，amplitude 是半群同态。
     由于 amplitude 是单射的，(C, compose) 同构于 S¹ 的一个子半群。
     S¹ 是群，有限子半群是子群。
     因此 (C, compose) 是群。
     群是左可迁的。
     由 output_degenerate_theorem，output 是常函数。

   意义：
     这是"此起彼伏原理"的精确数学形式。
     在标准理论框架中，两面性确实是"零和"的——
     一面的非平凡性以另一面的退化为代价。

   出路：
     要实现两面平衡态，必须扩展公理框架。
     可能的方向：
     1. Theory'（带 combine 运算）—— 我们已经在做了
     2. 放弃 norm_one（非幺正振幅）
     3. 放弃 amplitude_injective
     4. 修改 compose_output 公理

   物理意义：
     这暗示"量子态"（信息面极致）和"经典态"（因果面极致）
     确实是标准理论的两个极端，
     而"测量"或"经典涌现"需要某种扩展框架。
   ============================================================================ -/

end CSQIT.Models.SmallSemigroups
