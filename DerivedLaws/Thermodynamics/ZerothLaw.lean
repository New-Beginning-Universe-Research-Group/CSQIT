/-
CSQIT — 热力学第零定律（热平衡的传递性）
文件: DerivedLaws/Thermodynamics/ZerothLaw.lean
版本: v11.6.0
日期: 2026-07-19
编译状态: ⏸ 未参与编译（未在 lakefile.lean 中注册）

================================================================================
定律名称：热力学第零定律（热平衡的传递性）
================================================================================

物理中的对应：
  如果系统 A 与系统 B 处于热平衡，
  系统 B 与系统 C 处于热平衡，
  那么系统 A 与系统 C 也处于热平衡。

  这是"温度"概念存在的基础——
  正是因为热平衡是等价关系，
  我们才能给每个系统赋予一个"温度"的数值。

CSQIT 中的对应：
  热平衡 = 处于同一个"因果等温面"上
  （即两个事件之间没有确定的因果先后关系，或者它们的因果熵相同）

  在更基础的层面上：
  等价关系（自反性、对称性、传递性）
  是偏序结构的自然副产品。

依赖层级：🟢 W2 条件性定理
  数学核心（等价关系三性质）：🔵 W1 严格（从等式的自反/对称/传递直接推出）
  物理对应（= 热力学第零定律）：🟢 W2 条件性（需要"热平衡 = 因果熵相等"假设）

物理意义：
  热力学第零定律不是经验归纳，
  而是等价关系的数学性质。
  只要热平衡是由某种偏序定义的等价关系，
  传递性就是必然的。

适用范围：
  - 适用于所有由偏序定义的等价关系
  - 热平衡 = "处于同一熵水平" 是其中一种
  - 这是温度概念的代数基础
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
热平衡关系：两个事件处于热平衡当且仅当它们的因果熵相等。

这是热力学第零定律的代数基础——
热平衡 = 熵相等 = 处于同一个"等温面"上。
-/
def thermalEquilibrium (x y : M) : Prop :=
  causalEntropy x = causalEntropy y

/--
热力学第零定律：热平衡是等价关系。

等价关系三性质：
1. 自反性：x 与 x 自己热平衡
2. 对称性：若 x 与 y 热平衡，则 y 与 x 热平衡
3. 传递性：若 x 与 y 热平衡，y 与 z 热平衡，则 x 与 z 热平衡

正是这三条性质保证了"温度"概念的存在性——
我们可以给每个等价类赋予一个温度标签。
-/
theorem zerothLaw_thermalEquivalence :
    (∀ (x : M), thermalEquilibrium x x) ∧
    (∀ (x y : M), thermalEquilibrium x y → thermalEquilibrium y x) ∧
    (∀ (x y z : M), thermalEquilibrium x y → thermalEquilibrium y z → thermalEquilibrium x z) := by
  constructor
  · -- 自反性
    intro x
    rfl
  · constructor
    · -- 对称性
      intro x y h
      exact h.symm
    · -- 传递性
      intro x y z hxy hyz
      exact Eq.trans hxy hyz

/--
温度的存在性定理：
  可以为每个事件赋予一个"温度标签"（即因果熵的数值），
  使得两个事件热平衡当且仅当它们的温度标签相等。

这就是热力学第零定律的本质——
温度是等价类的标签。
-/
theorem temperature_exists :
    ∃ (T : M → ℕ), ∀ (x y : M), thermalEquilibrium x y ↔ T x = T y := by
  refine ⟨causalEntropy, ?_⟩
  intro x y
  rfl

/--
热平衡的另一种定义：因果不可比（类空间隔）。

在因果格中，两个事件如果不可比（¬ x ≤ y ∧ ¬ y ≤ x），
那么它们之间没有因果联系，
可以看作处于"同一时刻"的不同空间位置。

这与相对论中"类空事件的同时性"是同一思想。
-/
def spacelikeSeparation (x y : M) : Prop :=
  ¬ x ≤ y ∧ ¬ y ≤ x

/--
类空间隔的对称性：
  如果 x 与 y 类空间隔，那么 y 与 x 也类空间隔。
-/
theorem spacelikeSymmetric {x y : M} :
    spacelikeSeparation x y → spacelikeSeparation y x := by
  intro h
  exact ⟨h.2, h.1⟩

/--
类时间隔的定义：x 与 y 有确定的因果先后关系。

即 x ≤ y 或 y ≤ x。
-/
def timelikeSeparation (x y : M) : Prop :=
  x ≤ y ∨ y ≤ x

/--
因果二分定理：
  任意两个事件之间，要么是类时间隔，要么是类空间隔。

这是相对论因果结构的核心特征——
没有第三种可能。
-/
theorem causal_dichotomy (x y : M) :
    timelikeSeparation x y ∨ spacelikeSeparation x y := by
  by_cases h : x ≤ y
  · left
    exact Or.inl h
  · by_cases h' : y ≤ x
    · left
      exact Or.inr h'
    · right
      exact ⟨h, h'⟩

end CSQIT.DerivedLaws.Thermodynamics
