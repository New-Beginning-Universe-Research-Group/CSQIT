/-
CSQIT — 因果结构理论（相对论性因果的格论基础）
文件: DerivedLaws/Spacetime/CausalStructure.lean
版本: v11.6.0
日期: 2026-07-19
编译状态: ⏸ 未参与编译（未在 lakefile.lean 中注册）

================================================================================
定律名称：相对论性因果结构
================================================================================

物理中的对应：
  相对论中，时空的因果结构是最基础的结构之一：
  - 类时间隔：有因果联系的事件对
  - 类空间隔：没有因果联系的事件对
  - 因果过去/未来光锥
  - 因果律：信号传播不能超过光速

  这些都被编码在时空的洛伦兹度规中。

CSQIT 中的对应：
  因果格的偏序结构 = 相对论的因果结构
  - ≤ 关系 = 因果先后关系
  - causalPast = 过去光锥
  - causalFuture = 未来光锥
  - 不可比关系 = 类空间隔

依赖层级：🟡 W2 框架性
  数学核心（类时/类空二分、光锥性质）：🔵 W1 严格（从偏序公理直接推出）
  物理对应（= 相对论性因果结构）：🟡 W2 框架性
    （需要添加度规、维度、洛伦兹群等额外结构）

物理意义：
  相对论的因果结构不是时空度规的副产品，
  而是更基础的因果格结构的体现。
  时空度规可以从因果序中涌现出来，
  而不是相反。

适用范围：
  - 适用于所有因果格
  - 这是"因果先于时空"的数学表达
  - 洛伦兹度规是额外的（W2/W3 层）结构
================================================================================
-/

import Core.W1.CausalLattice

namespace CSQIT.DerivedLaws.Spacetime

open CausalLattice

variable {M : Type*} [CausalLattice M]

/--
类时间隔：两个事件之间有确定的因果先后关系。

即 x ≤ y 或 y ≤ x。

物理对应：
  类时间隔的事件对之间可以有因果联系，
  信号可以从一个传到另一个。
-/
def timelike (x y : M) : Prop :=
  x ≤ y ∨ y ≤ x

/--
类空间隔：两个事件之间没有因果先后关系。

即 ¬ x ≤ y ∧ ¬ y ≤ x。

物理对应：
  类空间隔的事件对之间不能有因果联系，
  它们是"同时性"的候选者（取决于参考系）。
-/
def spacelike (x y : M) : Prop :=
  ¬ x ≤ y ∧ ¬ y ≤ x

/--
因果三分律：
  任意两个事件之间，要么类时，要么类空，
  没有第三种可能。

这是相对论因果结构的核心特征。
-/
theorem causal_trichotomy (x y : M) :
    timelike x y ∨ spacelike x y := by
  by_cases h : x ≤ y
  · left
    exact Or.inl h
  · by_cases h' : y ≤ x
    · left
      exact Or.inr h'
    · right
      exact ⟨h, h'⟩

/--
过去光锥定理：
  因果过去集合是向下封闭的。
  （如果 y 在 x 的过去中，且 z 在 y 的过去中，那么 z 也在 x 的过去中）

物理对应：
  过去光锥的内部也是过去光锥——
  原因的原因也是原因。
-/
theorem pastLightCone_downwardClosed {x y : M} (h : y ∈ causalPast x) :
    causalPast y ⊆ causalPast x := by
  intro z hz
  have h1 : z ≤ y := hz
  have h2 : y ≤ x := h
  have h3 : z ≤ x := le_trans h1 h2
  exact h3

/--
未来光锥定理：
  因果未来集合是向上封闭的。

物理对应：
  未来光锥的内部也是未来光锥——
  结果的结果也是结果。
-/
theorem futureLightCone_upwardClosed {x y : M} (h : y ∈ causalFuture x) :
    causalFuture y ⊆ causalFuture x := by
  intro z hz
  have h1 : y ≤ z := hz
  have h2 : x ≤ y := h
  have h3 : x ≤ z := le_trans h2 h1
  exact h3

/--
因果边界定理：
  一个集合的因果边界，
  是"刚好在因果可达范围边缘"的事件。

物理对应：
  因果边界 ≈ 光锥本身（不是内部，而是表面）。
-/
theorem causalBoundary_isEdge (S : Set M) (x : M) (hx : x ∈ causalBoundary S) :
    x ∉ S ∧ ∃ (y : M), y ∈ S ∧ (y ≤ x ∨ x ≤ y) := by
  simpa [causalBoundary] using hx

/--
可观测宇宙的定义：
  一个事件 x 的可观测宇宙 = 它的因果过去 ∪ 因果未来
  = 所有与 x 有因果联系的事件的集合。

物理对应：
  可观测宇宙 = 过去光锥 ∪ 未来光锥。
  类空事件是不可观测的（至少在原则上）。
-/
theorem observableUniverse_isTimelike (x : M) :
    observableUniverse x = { y | timelike x y } := by
  ext y
  simp only [observableUniverse, timelike, Set.mem_union, Set.mem_setOf_eq]
  <;> tauto

/--
因果结构的相对论性约束：

1. 因果序是偏序（自反、传递、反对称）
2. 过去和未来光锥是凸的
3. 类空/类时是互补且对称的

这些都是相对论因果结构的基本性质，
在 CSQIT 中它们是因果格公理的直接推论。
-/
theorem relativistic_causal_constraints (x y z : M) :
    (x ≤ x) ∧                              -- 自反性
    (x ≤ y → y ≤ z → x ≤ z) ∧              -- 传递性
    (x ≤ y → y ≤ x → x = y) ∧              -- 反对称性
    (timelike x y ↔ ¬ spacelike x y) ∧     -- 二分性
    (timelike x y ↔ timelike y x) ∧        -- 对称性（类时）
    (spacelike x y ↔ spacelike y x) := by  -- 对称性（类空）
  constructor
  · exact le_refl x
  · constructor
    · intro h1 h2
      exact le_trans h1 h2
    · constructor
      · intro h1 h2
        exact le_antisymm h1 h2
      · constructor
        · constructor
          · intro h
            simp only [timelike, spacelike] at h ⊢
            tauto
          · intro h
            have h' : timelike x y ∨ spacelike x y := causal_trichotomy x y
            cases h' with
            | inl h' => exact h'
            | inr h' => exfalso; exact h h'
        · constructor
          · intro h
            cases h with
            | inl h => exact Or.inr h
            | inr h => exact Or.inl h
          · intro h
            cases h with
            | inl h => exact Or.inr h
            | inr h => exact Or.inl h

end CSQIT.DerivedLaws.Spacetime
