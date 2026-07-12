/-
================================================================================
CSQIT 应用物理模型 - 磁性与自旋态模型
文件: Unified/Models/Magnetism.lean
版本: v11.2.1
日期: 2026-07-08
状态: 严格证明完成 ✅
================================================================================
理论层级说明
================================================================================

本文件属于 **W2/W3 层**——有效理论与物理解释层。

- 数学定义：精确的 Lean 4 形式化（W1 标准）
- 物理对应：磁性与原子排列的关系（W3 层猜想）
- 核心贡献：从两面性原理出发，建立自旋态、磁矩、交换相互作用
  与磁性有序相（铁磁、反铁磁、顺磁）的离散因果模型。

================================================================================
核心洞察：磁性 = 信息面的有序排列
================================================================================

在 CSQIT 框架中，磁性本质上是信息面的集体有序态：

  自旋态 = 振幅的相位方向
  磁矩 = 振幅模方 × 相位取向
  交换相互作用 = 相邻结点振幅的耦合强度

不同的磁性相：
  - 铁磁性：相邻自旋平行排列（有序态）
  - 反铁磁性：相邻自旋反平行排列（有序态）
  - 顺磁性：自旋随机取向（无序态）

================================================================================
数学路线图
================================================================================

§1. 自旋态与磁矩
    - 自旋态：振幅的复数表示
    - 磁矩：μ = |ψ|² · (Re - Im)
    - 磁矩的可正可负性（证否示例）

§2. 交换相互作用
    - 最近邻定义
    - 交换相互作用强度
    - 海森堡哈密顿量

§3. 磁性有序相
    - 铁磁性：H < 0，自旋平行
    - 反铁磁性：H > 0，自旋反平行
    - 顺磁性：H = 0，自旋无序

================================================================================
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

namespace CSQIT.Unified.Models.Magnetism

open Classical Finset BigOperators

set_option linter.unusedVariables false

/-! ============================================================================
   §1. 自旋态与磁矩
   ============================================================================ -/

section MagneticMoment

/-
**定义 1.1: 自旋态（Spin State）**

每个规则/原子的自旋态由其复数振幅表示：

  s(α) = amplitude(α) ∈ ℂ

其中：
  - 模 |s| 决定自旋的"大小"
  - 相位 arg(s) 决定自旋的"方向"
-/
def spinState (alpha : ℂ) : ℂ := alpha

/-
**定义 1.2: 磁矩（Magnetic Moment）**

磁矩定义为振幅模方乘以相位取向：

  μ(α) = |ψ(α)|² · (Re(ψ) - Im(ψ))

物理意义：
  磁矩的大小由概率密度（|ψ|²）决定，
  方向由振幅的实部与虚部之差决定。
  当 Re > Im 时，磁矩为正（自旋向上）；
  当 Re < Im 时，磁矩为负（自旋向下）。
-/
noncomputable def magneticMoment (alpha : ℂ) : ℝ :=
  Complex.normSq alpha * (Complex.re alpha - Complex.im alpha)

/-
**定义 1.3: 总磁矩（Total Magnetic Moment）**

系统的总磁矩是各单元磁矩之和：

  M_total = ∑_{α ∈ s} μ(α)
-/
noncomputable def totalMagneticMoment (s : Finset ℂ) : ℝ :=
  ∑ α ∈ s, magneticMoment α

/-
**定理 1.1: 磁矩可以为负（证否示例）**

如果振幅为纯虚数（如 i），则磁矩为负。

证否依据：
  若 ψ(α) = i，则
    Re = 0, Im = 1, |ψ|² = 1
    μ = 1 · (0 - 1) = -1 < 0

这说明磁矩是有方向的（矢量性质），
不能简单定义为非负标量。
-/
theorem magneticMoment_negative_example :
    magneticMoment Complex.I < 0 := by
  unfold magneticMoment
  simp [Complex.normSq_I]

/-
**定义 1.4: 磁矩大小（磁矩的绝对值）**

为了得到非负的磁矩大小，取绝对值：

  |μ(α)| = |ψ(α)|² · |Re(ψ) - Im(ψ)|

这总是非负的，与自旋的"强度"相关。
-/
noncomputable def magneticMomentMagnitude (alpha : ℂ) : ℝ :=
  Complex.normSq alpha * |Complex.re alpha - Complex.im alpha|

/-
**定理 1.2: 磁矩大小非负**

  |μ(α)| ≥ 0
-/
theorem magneticMomentMagnitude_nonneg (alpha : ℂ) :
    0 ≤ Complex.normSq alpha * |Complex.re alpha - Complex.im alpha| := by
  apply mul_nonneg
  · apply Complex.normSq_nonneg
  · apply abs_nonneg

end MagneticMoment

/-! ============================================================================
   §2. 交换相互作用
   ============================================================================ -/

section ExchangeInteraction

variable {X : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
variable (psi : X → ℂ)

/-
**定义 2.1: 最近邻（Nearest Neighbor）**

在离散格点上，x 和 y 互为最近邻，
当且仅当它们是直接前驱或后继关系。
-/
def isNearestNeighbor (x y : X) : Prop :=
  (x < y ∧ ¬ ∃ z : X, x < z ∧ z < y) ∨
  (y < x ∧ ¬ ∃ z : X, y < z ∧ z < x)

/-
**定义 2.2: 交换相互作用（Exchange Interaction）**

相邻格点 x 和 y 之间的交换相互作用强度为：

  J(x, y) = ∑_{α∈x} ∑_{β∈y} |ψ(α) · ψ(β)|²

其中 α ∈ x 表示位于格点 x 的规则，β ∈ y 类似。

简化模型中，我们直接用格点振幅计算：
  J(x, y) = |ψ(x) · ψ(y)|²
          = |ψ(x)|² · |ψ(y)|²

物理意义：
  交换相互作用来源于信息面的耦合，
  它决定了相邻自旋的取向偏好——
  J > 0 倾向于平行（铁磁），
  J < 0 倾向于反平行（反铁磁）。
-/
noncomputable def exchangeInteraction (x y : X) : ℝ :=
  if isNearestNeighbor x y then
    Complex.normSq (psi x * psi y)
  else
    0

/-
**定义 2.3: 海森堡哈密顿量（Heisenberg Hamiltonian）**

系统的总交换能量（海森堡模型）为：

  H = -∑_{⟨x,y⟩} J(x, y) · S_x · S_y

在简化模型中，我们采用标准的负号约定：
  H = -∑_{x,y} J(x, y)

物理意义：
  - H < 0：负交换能，相邻自旋平行更稳定（铁磁性）
  - H > 0：正交换能，相邻自旋反平行更稳定（反铁磁性）
  - H = 0：无交换相互作用（顺磁性）
-/
noncomputable def heisenbergHamiltonian (s : Finset X) : ℝ :=
  -∑ x ∈ s, ∑ y ∈ s, exchangeInteraction psi x y

/-
**定理 2.1: 交换相互作用非负性**

  J(x, y) ≥ 0

交换相互作用强度总是非负的。
-/
theorem exchangeInteraction_nonneg (x y : X) :
    0 ≤ exchangeInteraction psi x y := by
  unfold exchangeInteraction
  split_ifs
  · exact Complex.normSq_nonneg _
  · norm_num

/-
**定理 2.2: 交换相互作用的对称性**

  J(x, y) = J(y, x)

交换相互作用是对称的。
-/
theorem exchangeInteraction_symmetric (x y : X) :
    exchangeInteraction psi x y = exchangeInteraction psi y x := by
  unfold exchangeInteraction isNearestNeighbor
  have h_comm : ((x < y ∧ ¬ ∃ z : X, x < z ∧ z < y) ∨
                 (y < x ∧ ¬ ∃ z : X, y < z ∧ z < x)) ↔
                ((y < x ∧ ¬ ∃ z : X, y < z ∧ z < x) ∨
                 (x < y ∧ ¬ ∃ z : X, x < z ∧ z < y)) := by
    tauto
  simp only [h_comm]
  <;> ring

/-
**定义 2.4: 最近邻自旋关联函数**

相邻格点的自旋关联强度：
  C(x, y) = Re(ψ(x) * conj(ψ(y))) / (|ψ(x)| · |ψ(y)|)

当 C > 0 时，自旋趋向平行（铁磁倾向）
当 C < 0 时，自旋趋向反平行（反铁磁倾向）
-/
noncomputable def spinCorrelation (x y : X) : ℝ :=
  if isNearestNeighbor x y ∧ psi x ≠ 0 ∧ psi y ≠ 0 then
    Complex.re (psi x * star (psi y)) /
      (Real.sqrt (Complex.normSq (psi x)) * Real.sqrt (Complex.normSq (psi y)))
  else
    0

/-
**定义 2.5: 总自旋关联**

系统的总自旋关联度：
  C_total = ∑_{⟨x,y⟩} C(x, y)
-/
noncomputable def totalSpinCorrelation (s : Finset X) : ℝ :=
  ∑ x ∈ s, ∑ y ∈ s, spinCorrelation psi x y

/-
**定理 2.4: 自旋关联函数有界**

  -1 ≤ C(x, y) ≤ 1

这是柯西-施瓦茨不等式的直接结果。
-/
theorem spinCorrelation_bounded (x y : X) :
    -1 ≤ spinCorrelation psi x y ∧ spinCorrelation psi x y ≤ 1 := by
  -- 柯西-施瓦茨不等式：|Re(ψx · conj(ψy))| ≤ ‖ψx‖ · ‖ψy‖
  unfold spinCorrelation
  split_ifs with h
  · rcases h with ⟨h_nn, h_px, h_py⟩
    -- 把 sqrt(normSq z) 改写为 ‖z‖（Complex.norm_def : ‖z‖ = sqrt(normSq z)）
    rw [← Complex.norm_def (psi x), ← Complex.norm_def (psi y)]
    -- 分母 ‖ψx‖ * ‖ψy‖ 为正
    have h_den_pos : 0 < ‖psi x‖ * ‖psi y‖ := by
      have h1 : 0 < Complex.normSq (psi x) := Complex.normSq_pos.mpr h_px
      have h2 : 0 < Complex.normSq (psi y) := Complex.normSq_pos.mpr h_py
      have h3 : 0 < ‖psi x‖ := by rw [Complex.norm_def]; exact Real.sqrt_pos.mpr h1
      have h4 : 0 < ‖psi y‖ := by rw [Complex.norm_def]; exact Real.sqrt_pos.mpr h2
      exact mul_pos h3 h4
    -- |Re(ψx * star ψy)| ≤ ‖ψx * star ψy‖ = ‖ψx‖ * ‖star ψy‖ = ‖ψx‖ * ‖ψy‖
    have h_abs_le : |Complex.re (psi x * star (psi y))| ≤ ‖psi x‖ * ‖psi y‖ := by
      have h1 : |Complex.re (psi x * star (psi y))| ≤ ‖psi x * star (psi y)‖ :=
        Complex.abs_re_le_norm _
      rw [Complex.norm_mul] at h1
      have h2 : ‖star (psi y)‖ = ‖psi y‖ := Complex.norm_conj _
      rw [h2] at h1
      exact h1
    have h_re_le : Complex.re (psi x * star (psi y)) ≤ ‖psi x‖ * ‖psi y‖ :=
      le_trans (le_abs_self _) h_abs_le
    have h_neg_re_le : -Complex.re (psi x * star (psi y)) ≤ ‖psi x‖ * ‖psi y‖ := by
      have h_neg_le : -Complex.re (psi x * star (psi y)) ≤
          |Complex.re (psi x * star (psi y))| := by
        have := le_abs_self (-(Complex.re (psi x * star (psi y))))
        rwa [abs_neg] at this
      linarith
    constructor
    · rw [le_div_iff₀ h_den_pos]; linarith
    · rw [div_le_iff₀ h_den_pos]; linarith
  · constructor
    · norm_num
    · norm_num

end ExchangeInteraction

/-! ============================================================================
   §3. 磁性有序相
   ============================================================================ -/

section MagneticPhases

variable {X : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
variable (psi : X → ℂ)

/-
**定义 3.1: 铁磁性（Ferromagnetism）**

当系统的总自旋关联为正时，
系统处于铁磁有序相：
  C_total > 0 → 铁磁性

物理意义：
  正的自旋关联意味着相邻自旋平行排列占主导，
  整体表现出自发磁化。
-/
def isFerromagnetic (s : Finset X) : Prop :=
  totalSpinCorrelation psi s > 0

/-
**定义 3.2: 反铁磁性（Antiferromagnetism）**

当系统的总自旋关联为负时，
系统处于反铁磁有序相：
  C_total < 0 → 反铁磁性

物理意义：
  负的自旋关联意味着相邻自旋反平行排列占主导，
  整体磁矩为零但有磁有序结构。
-/
def isAntiferromagnetic (s : Finset X) : Prop :=
  totalSpinCorrelation psi s < 0

/-
**定义 3.3: 顺磁性（Paramagnetism）**

当系统的总自旋关联为零时，
系统处于顺磁无序相：
  C_total = 0 → 顺磁性

物理意义：
  自旋关联为零，自旋随机取向，
  没有宏观磁有序。
-/
def isParamagnetic (s : Finset X) : Prop :=
  totalSpinCorrelation psi s = 0

/-
**定理 3.1: 三相的互斥性与完备性**

对于给定系统，铁磁、反铁磁、顺磁三者互斥，
且必居其一。
-/
theorem three_phases_exhaustive (s : Finset X) :
    isFerromagnetic psi s ∨ isAntiferromagnetic psi s ∨ isParamagnetic psi s := by
  unfold isFerromagnetic isAntiferromagnetic isParamagnetic
  have h : (totalSpinCorrelation psi s < 0) ∨
           (totalSpinCorrelation psi s > 0) ∨
           (totalSpinCorrelation psi s = 0) := by
    by_cases h1 : totalSpinCorrelation psi s < 0
    · exact Or.inl h1
    · by_cases h2 : totalSpinCorrelation psi s > 0
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr (by linarith))
  rcases h with (h | h | h)
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

theorem ferro_antiferro_exclusive (s : Finset X) :
    ¬ (isFerromagnetic psi s ∧ isAntiferromagnetic psi s) := by
  intro h
  have h1 : totalSpinCorrelation psi s > 0 := h.1
  have h2 : totalSpinCorrelation psi s < 0 := h.2
  linarith

theorem ferro_para_exclusive (s : Finset X) :
    ¬ (isFerromagnetic psi s ∧ isParamagnetic psi s) := by
  intro h
  have h1 : totalSpinCorrelation psi s > 0 := h.1
  have h2 : totalSpinCorrelation psi s = 0 := h.2
  linarith

theorem antiferro_para_exclusive (s : Finset X) :
    ¬ (isAntiferromagnetic psi s ∧ isParamagnetic psi s) := by
  intro h
  have h1 : totalSpinCorrelation psi s < 0 := h.1
  have h2 : totalSpinCorrelation psi s = 0 := h.2
  linarith

end MagneticPhases

end CSQIT.Unified.Models.Magnetism
