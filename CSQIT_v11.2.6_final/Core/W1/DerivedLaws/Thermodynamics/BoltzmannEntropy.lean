/-
CSQIT — 玻尔兹曼熵公式（因果熵到统计熵的桥梁）
文件: Core/W1/DerivedLaws/Thermodynamics/BoltzmannEntropy.lean
版本: v11.6.0
日期: 2026-07-19

================================================================================
定律名称：玻尔兹曼熵公式 S = k ln Ω
================================================================================

物理中的对应：
  系统的熵 = k × ln(微观态数)
  S = k_B · ln Ω

  这是统计力学的核心公式，
  连接了宏观热力学与微观力学。
  玻尔兹曼常数 k_B 是热力学与统计力学的桥梁。

CSQIT 中的对应：
  因果熵（causalEntropy） = 因果过去集合的大小
  统计熵 = k × ln(微观态数)

  两者的关系：
  因果熵是微观态数的对数的离散版本，
  或者说，微观态数 = exp(因果熵 / k)

  更深入地：
    因果熵（组合计数）
        ↓ 取对数 + 乘玻尔兹曼常数
    热力学熵

依赖层级：
  - 因果熵的定义与单调性：🔵 W1 严格定理
  - 玻尔兹曼公式（对数关系）：🟢 W2 条件性
    （需要"宏观态对应微观态集合"的假设）
  - 与热力学熵的等同：🟠 W3 诠释

物理意义：
  熵为什么是对数的？
  因为两个独立系统的微观态数相乘，
  而熵相加（广延量）。
  对数是唯一满足 f(xy) = f(x) + f(y) 的连续函数。

  在 CSQIT 中，因果熵天然是"可加的"（通过并集），
  而微观态数天然是"可乘的"（通过笛卡尔积），
  对数就是它们之间的翻译。

适用范围：
  - 因果熵的单调性：严格成立（W1）
  - 玻尔兹曼公式的形式：W2 条件性
  - 与热力学熵的等同：W3 诠释
================================================================================
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Core.W1.CausalLattice

namespace CSQIT.DerivedLaws.Thermodynamics

open CausalLattice

variable {M : Type*} [BoundedCausalLattice M] [Fintype M]

/--
因果熵的定义（离散版本，与 SecondLaw.lean 一致）：
  一个事件的因果熵 = 其因果过去集合的基数。

这是熵的最纯粹形式——
不涉及概率、不涉及统计，
只是因果历史的大小。
-/
def causalEntropy (x : M) : ℕ :=
  (Finset.univ.filter (· ∈ causalPast x)).card

/--
因果熵的单调性（W1 严格定理）：
  若 x ≤ y，则 causalEntropy x ≤ causalEntropy y。

这是热力学第二定律的因果格版本。
-/
theorem causalEntropy_monotone {x y : M} (h : x ≤ y) :
    causalEntropy x ≤ causalEntropy y := by
  have h1 : causalPast x ⊆ causalPast y := causalPast_downward_closed h
  have h2 : (Finset.univ.filter (· ∈ causalPast x)) ⊆ (Finset.univ.filter (· ∈ causalPast y)) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact h1 hz
  exact Finset.card_le_card h2

/--
微观态数（Ω）的定义：
  与给定宏观态（因果熵）相容的微观态的数量。

最简单的假设：
  Ω(x) = 2^{causalEntropy(x)}
  （每个因果过去事件有两种状态）

或者更一般地：
  Ω(x) = f(causalEntropy(x))
  其中 f 是某个递增函数。
-/
def microstateCount (x : M) : ℕ :=
  2 ^ causalEntropy x

/--
玻尔兹曼熵公式：
  S = k_B × ln(Ω)

离散版本（用 log 代替 ln，用 k 代替 k_B）：
  S_Boltzmann(x) = k * Real.log (microstateCount x)

这是连接因果熵与统计熵的桥梁。
-/
def boltzmannEntropy (k : ℝ) (x : M) : ℝ :=
  k * Real.log (microstateCount x : ℝ)

/--
玻尔兹曼熵的单调性：
  如果 x ≤ y，则 S_Boltzmann(x) ≤ S_Boltzmann(y)

因为：
  1. causalEntropy 是单调递增的
  2. microstateCount = 2^{causalEntropy} 也是单调递增的
  3. log 是单调递增的
  4. 乘以正的 k 保持单调性

所以玻尔兹曼熵自然满足热力学第二定律。
-/
theorem boltzmannEntropy_monotone (k : ℝ) (hk : 0 < k) {x y : M} (h : x ≤ y) :
    boltzmannEntropy k x ≤ boltzmannEntropy k y := by
  have h1 : causalEntropy x ≤ causalEntropy y := causalEntropy_monotone h
  have h2 : (2 : ℝ) ^ causalEntropy x ≤ (2 : ℝ) ^ causalEntropy y := by
    apply Real.pow_le_pow_of_le_left (by norm_num) h1
  have h3 : Real.log ((2 : ℝ) ^ causalEntropy x) ≤ Real.log ((2 : ℝ) ^ causalEntropy y) := by
    apply Real.log_le_log
    · positivity
    · exact h2
  have h4 : k * Real.log ((2 : ℝ) ^ causalEntropy x) ≤ k * Real.log ((2 : ℝ) ^ causalEntropy y) := by
    exact mul_le_mul_of_nonneg_left h3 (by linarith)
  simpa [boltzmannEntropy, microstateCount] using h4

/--
熵的广延性（可加性）：

对于两个独立系统 A 和 B：
  S_total = S_A + S_B

这来自于：
  Ω_total = Ω_A × Ω_B
  ln(Ω_A × Ω_B) = ln(Ω_A) + ln(Ω_B)

这就是为什么熵是对数的——
它把乘法变成加法，
从而满足广延性。
-/
theorem entropy_extensive (k : ℝ) (x y : M) :
    boltzmannEntropy k x + boltzmannEntropy k y =
    k * Real.log ((microstateCount x : ℝ) * (microstateCount y : ℝ)) := by
  have h1 : (microstateCount x : ℝ) > 0 := by positivity
  have h2 : (microstateCount y : ℝ) > 0 := by positivity
  simp [boltzmannEntropy, Real.log_mul h1 h2]
  <;> ring

/--
因果熵 vs 玻尔兹曼熵的关系：

  因果熵（离散，计数）
       ↑ 取指数
       |
  微观态数 Ω
       | 取对数 × k
       ↓
  玻尔兹曼熵（连续，热力学）

因果熵是更基础的概念，
玻尔兹曼熵是它在宏观/连续极限下的表现形式。
-/
def entropy_hierarchy : Prop := True

/--
玻尔兹曼常数 k_B 的 CSQIT 诠释：

k_B 是"因果熵"到"热力学熵"的转换系数。
它的存在是因为我们用不同的单位测量因果复杂度和热能。

从 CSQIT 角度看，
k_B 不是一个"基本常数"，
而是一个"单位转换因子"——
就像把英寸转换成厘米的因子一样。

更深刻地：
  k_B = 热力学熵的单位 / 因果熵的单位
-/
def boltzmannConstant_interpretation : Prop := True

end CSQIT.DerivedLaws.Thermodynamics
