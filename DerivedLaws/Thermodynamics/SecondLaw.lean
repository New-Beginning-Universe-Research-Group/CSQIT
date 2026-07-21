/-
CSQIT — 热力学第二定律（熵增原理的因果格本质）
文件: DerivedLaws/Thermodynamics/SecondLaw.lean
版本: v11.2.4
日期: 2026-07-19
编译状态: ⏸ 未参与编译（未在 lakefile.lean 中注册）

================================================================================
定律名称：热力学第二定律（熵增原理）
================================================================================

物理中的对应：
  孤立系统的熵永不减少。
  这是物理学中最基本的时间箭头——
  它区分了过去和未来，解释了为什么我们记得过去而不是未来。

CSQIT 中的对应：
  因果过去集合是下闭的（向下封闭的），
  因此，当你沿着因果序向上走（向未来前进），
  你的因果过去集合只会变大，不会变小。
  熵作为因果过去集合大小的度量，自然单调不减。

依赖层级：🟢 W2 条件性定理
  数学核心（因果熵单调性）：🔵 W1 严格（从因果过去下闭性直接推出）
  物理对应（= 热力学第二定律）：🟢 W2 条件性（需要"因果熵 = 热力学熵"假设）

物理意义：
  热力学第二定律不是一个"经验定律"，
  而是因果序结构的数学必然。
  时间有箭头，是因为因果有方向；
  熵只增不减，是因为因果过去只增不减。

适用范围：
  - 适用于所有有界因果格
  - 熵的定义是因果过去集合的基数（或其函数）
  - 在更复杂的模型中，熵的具体形式可能变化，
    但"随因果序单调不减"这一核心性质保持不变
================================================================================
-/

import Core.W1.CausalLattice

namespace CSQIT.DerivedLaws.Thermodynamics

open CausalLattice

variable {M : Type*} [BoundedCausalLattice M] [Fintype M]

/--
因果熵的定义：
  一个事件 x 的因果熵 = 其因果过去集合的基数。

这是最基础的熵定义——熵就是"因果历史的大小"。
物理中的热力学熵是这个概念在宏观极限下的表现。
-/
def causalEntropy (x : M) : ℕ :=
  (Finset.univ.filter (· ∈ causalPast x)).card

/--
热力学第二定律（因果版本）：
  如果 x ≤ y（x 在 y 的因果过去），
  那么 x 的因果熵 ≤ y 的因果熵。

这是熵增原理的最纯粹形式——
不是"系统倾向于无序"，而是"因果历史只增不减"。
-/
theorem causalEntropy_monotone {x y : M} (h : x ≤ y) :
    causalEntropy x ≤ causalEntropy y := by
  have h1 : causalPast x ⊆ causalPast y := by
    exact causalPast_downward_closed h
  have h2 : (Finset.univ.filter (· ∈ causalPast x)) ⊆ (Finset.univ.filter (· ∈ causalPast y)) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact h1 hz
  exact Finset.card_le_card h2

/--
推论：时间箭头是因果序的直接结果。

在因果格中，"朝向未来"就是"沿着 ≤ 向上走"，
而沿着 ≤ 向上走，熵单调不减。
因此，时间箭头（过去→未来）与熵增箭头完全一致。
-/
theorem time_arrow_matches_entropy_arrow (x y : M) (h : x ≤ y) :
    causalEntropy x ≤ causalEntropy y :=
  causalEntropy_monotone h

/--
过去假设的因果格版本：
  宇宙存在一个最小元（初始边界），它的因果熵最小。

这是"过去假设"（Past Hypothesis）的代数形式——
宇宙始于一个低熵的初始状态，
不是因为巧合，而是因为因果格有下界。
-/
theorem past_hypothesis_is_theorem :
    ∃ (x₀ : M), ∀ (x : M), causalEntropy x₀ ≤ causalEntropy x := by
  refine ⟨⊥, fun x => ?_⟩
  exact causalEntropy_monotone (bot_le x)

end CSQIT.DerivedLaws.Thermodynamics
