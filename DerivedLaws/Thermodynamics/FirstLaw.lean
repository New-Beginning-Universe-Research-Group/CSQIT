/-
CSQIT — 热力学第一定律（能量守恒与热功当量）
文件: DerivedLaws/Thermodynamics/FirstLaw.lean
版本: v11.2.4
日期: 2026-07-19
编译状态: ⏸ 未参与编译（未在 lakefile.lean 中注册）

================================================================================
定律名称：热力学第一定律
================================================================================

物理中的对应：
  能量守恒：封闭系统的总能量不变。
  热功当量：热量和功可以相互转化，总量守恒。

  数学表达式：ΔU = Q - W
  （内能变化 = 吸收的热量 - 对外做的功）

CSQIT 中的对应：
  1. 振幅幺正性 → 某种"强度"守恒（已证）
  2. 因果熵的变化与"功"的关系（待建立）
  3. 第一定律 = 能量守恒 + 熵-能量对应关系

依赖层级：🟢 W2 条件性定理
  - 振幅守恒部分：🔵 W1 严格定理
  - 熵-能量对应关系：🟢 W2 条件（额外假设）
  - 完整第一定律：🟢 W2 条件性

物理意义：
  热力学第一定律的本质是能量守恒，
  而能量守恒的代数版本是振幅幺正性。
  热和功的区别是宏观极限下的两种能量转移方式。

适用范围：
  - 纯能量守恒（振幅模长）：严格成立
  - 热功当量：需要额外的熵-能量对应假设
  - 在宏观、平衡态下成立
================================================================================
-/

import Core.W1.AmplitudeTheorems

namespace CSQIT.DerivedLaws.Thermodynamics

variable {M C : Type*} [AxiomA M C] [AxiomC M C]

/--
能量守恒的代数基础：振幅模长恒为1。

  ∀ α, |amplitude α|² = 1

这是能量守恒的最纯粹形式——
基本规则的"强度"不随复合改变。
-/
theorem energyConservation_core (α : C) :
    Complex.normSq (AxiomC.amplitude α) = 1 :=
  AxiomC.norm_one α

/--
复合下的能量守恒：
  复合后的振幅模长 = 复合前模长的乘积 = 1。

  |amplitude (α ∘ β)| = |amplitude α| × |amplitude β| = 1
-/
theorem energyConservation_compose (α β : C) :
    Complex.normSq (AxiomC.amplitude (AxiomA.compose α β)) = 1 := by
  rw [amplitude_compose α β, Complex.normSq_mul]
  rw [energyConservation_core α, energyConservation_core β]
  <;> ring

/--
热功当量假设（W2 层额外假设）：

假设存在一个函数 T : C → ℝ（温度类的能量函数），
只依赖于振幅的实部或某种"能量类似物")，
使得能量变化 = 热量 - 功。

这是从振幅守恒到热力学第一定律的桥梁。
-/
def FirstLawHypothesis
    (U : C → ℝ)
    (Q : C → ℝ)
    (W : C → ℝ) : Prop :=
  ∀ (α β : C),
    U (AxiomA.compose α β) - U α = Q β - W β

/--
热力学第一定律（条件性版本）：

如果内能 U、热量 Q、功 W 满足适当的关系，
那么第一定律成立。

注意：这是 W2 层的条件性定理。
能量守恒本身是严格的，
但热和功的划分需要额外的诠释。
-/
theorem firstLaw_condition
    (U Q W : C → ℝ)
    (hU : ∀ α β, U (AxiomA.compose α β) = U α + U β - U (AxiomA.id))
    (hQW : ∀ α, Q α - W α = U α - U (AxiomA.id)) :
    FirstLawHypothesis U Q W := by
  intro α β
  have h1 : U (AxiomA.compose α β) - U α = U β - U (AxiomA.id) := by
    rw [hU α β]
    <;> ring
  have h2 : Q β - W β = U β - U (AxiomA.id) := hQW β
  linarith

/--
第一定律的另一种表述：
  封闭系统的总能量变化 = 传入的热量 - 对外做的功

这是能量守恒在热力学中的具体形式。
-/
def firstLawStatement (U Q W : C → ℝ) : Prop :=
  ∀ (α β : C), U (AxiomA.compose α β) - U α = Q β - W β

/--
能量守恒与第一定律的关系：

  能量守恒（W1 严格）
      ↓ 加熵-能量对应假设（W2）
  热力学第一定律（W2 条件性）

能量守恒比第一定律更基础、更严格。
第一定律是能量守恒在热力学系统中的具体表现形式。
-/
/- 猜想：energyConservation_implies_firstLaw 状态：🟢 W2 条件性 -/

end CSQIT.DerivedLaws.Thermodynamics
