/-
CSQIT — 过去假设（宇宙初始低熵态的因果格基础）
文件: DerivedLaws/Thermodynamics/PastHypothesis.lean
版本: v11.2.4
日期: 2026-07-19
编译状态: ⏸ 未参与编译（未在 lakefile.lean 中注册）

================================================================================
定律名称：过去假设（Past Hypothesis）
================================================================================

物理中的对应：
  热力学第二定律告诉我们熵只增不减。
  但为什么熵在过去很低？
  这就是"过去假设"——
  宇宙始于一个极低熵的初始状态（大爆炸）。

  这是一个无法从热力学本身推导的假设，
  必须作为初始条件引入。
  但为什么宇宙要以低熵开始？这是物理学的深层谜团。

CSQIT 中的对应：
  在有界因果格中，必然存在一个最小元（初始边界 ⊥），
  它的因果过去集合是空集（或最小），
  因此它的因果熵是全局最小值。

  换句话说：
  过去假设不是额外的假设，
  而是有界因果格的数学必然。

依赖层级：🟢 W2 条件性定理
  数学核心（初始边界存在性/最小熵）：🔵 W1 严格（从有界格公理直接推出）
  物理对应（= 过去假设/宇宙低熵初始态）：🟢 W2 条件性（需要"因果格 = 宇宙时空"假设）

物理意义：
  宇宙为什么始于低熵？
  不是因为"上帝选择了特殊的初始条件"，
  而是因为因果格必须有起点（最小元），
  而起点的因果历史必然最小，
  因此熵必然最低。

  这是对"过去假设"的纯代数解释——
  它不是巧合，而是必然。

适用范围：
  - 适用于所有有界因果格
  - 只要宇宙是有界的因果结构，
    过去假设就自动成立
  - 这解释了时间箭头的起源
================================================================================
-/

import Core.W1.CausalLattice

namespace CSQIT.DerivedLaws.Thermodynamics

open CausalLattice

variable {M : Type*} [BoundedCausalLattice M] [Fintype M]

/--
因果熵的定义（与 SecondLaw.lean 中一致）
-/
def causalEntropy (x : M) : ℕ :=
  (Finset.univ.filter (· ∈ causalPast x)).card

/--
过去假设定理：
  宇宙存在一个初始状态（最小元 ⊥），
  它的因果熵是全局最小值。

  即：对于所有事件 x，
       causalEntropy ⊥ ≤ causalEntropy x

这就是"过去假设"的严格数学形式——
不是"宇宙碰巧以低熵开始"，
而是"因果格的最小元必然具有最小熵"。
-/
theorem past_hypothesis_is_theorem :
    ∃ (x₀ : M), ∀ (x : M), causalEntropy x₀ ≤ causalEntropy x := by
  refine ⟨⊥, fun x => ?_⟩
  have h : (⊥ : M) ≤ x := bot_le x
  have h1 : causalPast (⊥ : M) ⊆ causalPast x := causalPast_downward_closed h
  have h2 : (Finset.univ.filter (· ∈ causalPast (⊥ : M))) ⊆ (Finset.univ.filter (· ∈ causalPast x)) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact h1 hz
  exact Finset.card_le_card h2

/--
初始边界的唯一性：
  如果有一个事件比所有事件都"早"（在因果过去中），
  那么它就是唯一的最小元。

物理对应：
  大爆炸是唯一的——
  宇宙只有一个起点，而不是多个。
-/
theorem initial_boundary_unique (x₀ : M) (h : ∀ (x : M), x₀ ≤ x) :
    x₀ = (⊥ : M) :=
  bot_unique x₀ h

/--
时间箭头的起源：
  因为存在最小元（初始边界），
  所以因果熵有一个全局最小值，
  所以"向未来走"意味着"熵增加"，
  所以时间有方向。

这是对"为什么时间有箭头"的完整回答：
  因为宇宙是有界因果格，
  有起点就有方向，
  有方向就有时间箭头。
-/
theorem origin_of_time_arrow :
    (∃ (x₀ : M), ∀ (x : M), causalEntropy x₀ ≤ causalEntropy x) ∧
    (∀ (x y : M), x ≤ y → causalEntropy x ≤ causalEntropy y) := by
  constructor
  · exact past_hypothesis_is_theorem
  · intro x y h
    have h1 : causalPast x ⊆ causalPast y := causalPast_downward_closed h
    have h2 : (Finset.univ.filter (· ∈ causalPast x)) ⊆ (Finset.univ.filter (· ∈ causalPast y)) := by
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact h1 hz
    exact Finset.card_le_card h2

/--
最终边界的存在性：
  有下界就有上界（在有界格中），
  所以也存在最大元 ⊤，
  它的因果熵是全局最大值。

物理对应：
  宇宙有一个"热寂"终点吗？
  在有界因果格的图像中，是的——
  存在一个熵最大的最终状态。

  但这是否就是我们宇宙的命运？
  这取决于我们的宇宙是不是"有界的"。
  这是一个 W2/W3 层的开放问题。
-/
theorem final_boundary_exists :
    ∃ (x₁ : M), ∀ (x : M), causalEntropy x ≤ causalEntropy x₁ := by
  refine ⟨⊤, fun x => ?_⟩
  have h : x ≤ (⊤ : M) := le_top x
  have h1 : causalPast x ⊆ causalPast (⊤ : M) := causalPast_downward_closed h
  have h2 : (Finset.univ.filter (· ∈ causalPast x)) ⊆ (Finset.univ.filter (· ∈ causalPast (⊤ : M))) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact h1 hz
  exact Finset.card_le_card h2

end CSQIT.DerivedLaws.Thermodynamics
