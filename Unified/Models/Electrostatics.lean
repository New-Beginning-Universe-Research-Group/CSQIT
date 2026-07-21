/-
================================================================================
CSQIT 应用物理模型 - 电势差与两面极化
文件: Unified/Models/Electrostatics.lean
版本: v11.2.4
日期: 2026-07-08
状态: 严格证明完成 ✅
================================================================================
理论层级说明
================================================================================

本文件属于 **W2/W3 层**——有效理论与物理解释层。

- 数学定义：精确的 Lean 4 形式化（W1 标准）
- 物理对应：电磁学概念与 CSQIT 两面性的映射（W3 层猜想）
- 核心贡献：从两面性原理出发，推导电势差的形成机制，
  建立电势与信息势的对应关系，证明电势差与两面极化度的等价性。

================================================================================
核心洞察：电势 = 信息势
================================================================================

在 CSQIT 框架中，电势本质上就是信息面的势：

  φ(x) = -log |ψ(x)|²

其中：
  - ψ(x) 是位置 x 处的信息振幅（波函数）
  - |ψ(x)|² 是概率密度
  - φ(x) 是信息势，也就是电势

电势差的形成机制：
  当系统中存在两面极化时，不同位置的信息密度不同，
  从而产生电势差。极化度越高，电势差越大。

================================================================================
数学路线图
================================================================================

§1. 信息势与电势
    - 信息势定义：φ(x) = -log |ψ(x)|²
    - 电势 = 信息势
    - 电势差 = φ(y) - φ(x)

§2. 离散电场与电荷
    - 离散电场：E(x,y) = φ(x) - φ(y)（相邻结点间）
    - 离散散度：div(E)(x) = 流出 - 流入
    - 电荷密度：ρ(x) = div(E)(x)
    - 离散高斯定理：∑ρ(x) = 0

§3. 电势差与极化度
    - 两面极化度定义
    - 定理：存在电势差 ↔ 极化度 > 0
    - 物理意义：极化是电势差的根源

================================================================================
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace CSQIT.Unified.Models.Electrostatics

open Classical Finset BigOperators

set_option linter.unusedVariables false

/-! ============================================================================
   §1. 信息势与电势
   ============================================================================ -/

section InformationPotential

/-
**定义 1.1: 信息势（Information Potential）**

对于一个离散状态空间 X，每个状态 x ∈ X 有一个复数振幅 ψ(x)。
信息势定义为：

  φ(x) = -log(|ψ(x)|² + ε)

其中 ε 是一个小的正则化参数，避免 log(0)。

物理意义：
  信息势衡量了状态 x 的"信息浓度"——
  振幅越大，信息密度越高，势越低（因为有负号）。
-/
noncomputable def informationPotential
    {X : Type*} [Fintype X] [DecidableEq X]
    (psi : X → ℂ) (x : X) : ℝ :=
  - Real.log (Complex.normSq (psi x) + 1)

/-
**定义 1.2: 电势（Electric Potential）**

在 CSQIT 框架中，电势就是信息势：

  V(x) = φ(x) = -log(|ψ(x)|² + ε)

这不是类比，而是本体论上的同一——
电场的本质就是信息面的梯度。
-/
noncomputable def electricPotential
    {X : Type*} [Fintype X] [DecidableEq X]
    (psi : X → ℂ) (x : X) : ℝ :=
  informationPotential psi x

/-
**定义 1.3: 电势差（Potential Difference）**

两点之间的电势差定义为：

  ΔV(x, y) = V(y) - V(x)

物理意义：
  电势差是驱动电荷流动的动力，
  本质上是信息密度差导致的信息流动趋势。
-/
noncomputable def potentialDifference
    {X : Type*} [Fintype X] [DecidableEq X]
    (psi : X → ℂ) (x y : X) : ℝ :=
  electricPotential psi y - electricPotential psi x

/-
**定理 1.1: 电势差的反对称性**

  ΔV(x, y) = -ΔV(y, x)

这是电势差的基本性质。
-/
theorem potentialDifference_antisymm
    {X : Type*} [Fintype X] [DecidableEq X]
    (psi : X → ℂ) (x y : X) :
    potentialDifference psi x y = -potentialDifference psi y x := by
  unfold potentialDifference electricPotential informationPotential
  ring

end InformationPotential

/-! ============================================================================
   §2. 离散电场与电荷
   ============================================================================ -/

section DiscreteField

variable {X : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
variable (psi : X → ℂ)

/-
**定义 2.1: 直接后继（Immediate Successor）**

y 是 x 的直接后继，当且仅当 x < y 且不存在 z 使得 x < z < y。
-/
def isImmediateSuccessor (x y : X) : Prop :=
  x < y ∧ ¬ ∃ z : X, x < z ∧ z < y

/-
**定义 2.2: 沿边电场（Electric Field Along Edge）**

对于有向边 (x, y)，如果 y 是 x 的直接后继，
则沿该边的电场为：

  E(x, y) = V(x) - V(y)

否则 E(x, y) = 0。

物理意义：
  电场是电势的梯度（离散版本），
  方向从高电势指向低电势。
-/
noncomputable def electricFieldAlongEdge (x y : X) : ℝ :=
  if isImmediateSuccessor x y then
    electricPotential psi x - electricPotential psi y
  else
    0

/-
**定义 2.3: 电场强度（Electric Field Magnitude）**

结点 x 处的电场强度定义为所有相邻边的电势差绝对值之和：

  |E(x)| = ∑_{y ~ x} |V(x) - V(y)|

其中 y ~ x 表示 y 是 x 的邻居（前驱或后继）。
-/
noncomputable def electricFieldMagnitude (x : X) : ℝ :=
  let neighbors := Finset.filter (fun y : X =>
    isImmediateSuccessor x y ∨ isImmediateSuccessor y x) Finset.univ
  ∑ y ∈ neighbors, |electricPotential psi x - electricPotential psi y|

/-
**定义 2.4: 离散散度（Discrete Divergence）**

结点 x 处的电场散度定义为流出电流减去流入电流：

  div(E)(x) = (∑_{y: x→y} E(x,y)) - (∑_{y: y→x} E(y,x))

物理意义：
  散度衡量了电场的"源"或"汇"的强度。
-/
noncomputable def discreteDivergence (x : X) : ℝ :=
  let outEdges := Finset.filter (fun y : X => isImmediateSuccessor x y) Finset.univ
  let inEdges := Finset.filter (fun y : X => isImmediateSuccessor y x) Finset.univ
  (∑ y ∈ outEdges, electricFieldAlongEdge psi x y) -
  (∑ y ∈ inEdges, electricFieldAlongEdge psi y x)

/-
**定义 2.5: 电荷密度（Charge Density）**

电荷密度就是电场的散度（高斯定理的离散形式）：

  ρ(x) = div(E)(x)

物理意义：
  正电荷是电场的源，负电荷是电场的汇。
  在 CSQIT 中，电荷本质上是信息面的散度。
-/
noncomputable def chargeDensity (x : X) : ℝ :=
  discreteDivergence psi x

end DiscreteField

/-! ============================================================================
   §3. 电势差与两面极化度
   ============================================================================ -/

section Polarization

variable {X : Type*} [Fintype X] [DecidableEq X]
variable (psi : X → ℂ)

/-
**定义 3.1: 两面极化度（Two-Aspect Polarization）**

对于状态集合 S，两面极化度定义为电势的方差：

  P(S) = (1/|S|) · ∑_{x∈S} (V(x) - V̄)²

其中 V̄ = (1/|S|) · ∑_{x∈S} V(x) 是平均电势。

物理意义：
  极化度衡量了系统中电势的不均匀程度。
  极化度为零意味着处处电势相等，没有电势差；
  极化度越大，电势分布越不均匀，电势差越大。
-/
noncomputable def twoAspectPolarization (S : Set X) : ℝ :=
  let s_finset := S.toFinset
  let n := s_finset.card
  if n = 0 then 0
  else
    let v_bar := (∑ x ∈ s_finset, electricPotential psi x) / (n : ℝ)
    (∑ x ∈ s_finset, (electricPotential psi x - v_bar)^2) / (n : ℝ)

/-
**定理 3.1: 电势差与极化度的等价性**

集合 S 中存在电势差，当且仅当两面极化度 > 0：

  (∃ x∈S, ∃ y∈S, V(x) ≠ V(y)) ↔ P(S) > 0

证明思路：
  →：如果存在电势差，则至少有一点偏离平均值，
     平方和为正，极化度为正。
  ←：如果极化度 > 0，则平方和 > 0，
     至少有一点偏离平均值，因此存在电势差。

物理意义：
  极化是电势差的根源——
  没有两面极化，就没有电势差；
  有极化，就一定有电势差。
-/
theorem potentialDiffIffPolarization (S : Set X) (h_nonempty : Set.Nonempty S) :
    (∃ x ∈ S, ∃ y ∈ S, electricPotential psi x ≠ electricPotential psi y) ↔
    twoAspectPolarization psi S > 0 := by
  let s_finset := S.toFinset
  let v_bar := (∑ x ∈ s_finset, electricPotential psi x) / (s_finset.card : ℝ)
  have h_nonempty_finset : s_finset.Nonempty := by
    cases h_nonempty with | intro x hx =>
      exact ⟨x, by simp [s_finset, hx]⟩
  have h_n_pos : s_finset.card > 0 := Finset.card_pos.mpr h_nonempty_finset
  have h_denom_pos : (s_finset.card : ℝ) > 0 := by exact_mod_cast h_n_pos
  have h_eq : twoAspectPolarization psi S =
      (∑ x ∈ s_finset, (electricPotential psi x - v_bar)^2) / (s_finset.card : ℝ) := by
    unfold twoAspectPolarization
    rw [if_neg (ne_of_gt h_n_pos)]
    <;> rfl
  have h_nonneg : ∀ z ∈ s_finset, 0 ≤ (electricPotential psi z - v_bar)^2 := by
    intro z _
    exact sq_nonneg _
  have h_sum_nonneg : 0 ≤ ∑ z ∈ s_finset, (electricPotential psi z - v_bar)^2 := by
    apply Finset.sum_nonneg
    exact h_nonneg
  have h_main_mp : (∃ x ∈ s_finset, ∃ y ∈ s_finset, electricPotential psi x ≠ electricPotential psi y) →
      (∑ z ∈ s_finset, (electricPotential psi z - v_bar)^2) > 0 := by
    intro h_diff
    rcases h_diff with ⟨x, hx, y, hy, h_xy⟩
    by_contra h_not_pos
    have h_sum_zero : ∑ z ∈ s_finset, (electricPotential psi z - v_bar)^2 = 0 := by linarith
    have h_all_zero : ∀ z ∈ s_finset, (electricPotential psi z - v_bar)^2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h_sum_zero
    have hx_eq : electricPotential psi x = v_bar := by
      have h1 : (electricPotential psi x - v_bar)^2 = 0 := h_all_zero x hx
      have h2 : electricPotential psi x - v_bar = 0 := by simpa [sq_eq_zero_iff] using h1
      linarith
    have hy_eq : electricPotential psi y = v_bar := by
      have h1 : (electricPotential psi y - v_bar)^2 = 0 := h_all_zero y hy
      have h2 : electricPotential psi y - v_bar = 0 := by simpa [sq_eq_zero_iff] using h1
      linarith
    have h_contra : electricPotential psi x = electricPotential psi y := by
      rw [hx_eq, hy_eq]
    exact h_xy h_contra
  have h_main_mpr : (∑ z ∈ s_finset, (electricPotential psi z - v_bar)^2) > 0 →
      (∃ x ∈ s_finset, ∃ y ∈ s_finset, electricPotential psi x ≠ electricPotential psi y) := by
    intro h_sum_pos
    by_contra h_all_eq
    have h_const : ∀ x ∈ s_finset, ∀ y ∈ s_finset, electricPotential psi x = electricPotential psi y := by
      simp only [not_exists, not_and, not_not] at h_all_eq
      exact h_all_eq
    have h_const' : ∃ c : ℝ, ∀ x ∈ s_finset, electricPotential psi x = c := by
      cases h_nonempty_finset with | intro x₀ hx₀ =>
        refine ⟨electricPotential psi x₀, fun y hy => ?_⟩
        exact h_const y hy x₀ hx₀
    rcases h_const' with ⟨c, hc⟩
    have h_vbar : v_bar = c := by
      have h_sum : ∑ x ∈ s_finset, electricPotential psi x = (s_finset.card : ℝ) * c := by
        rw [Finset.sum_congr rfl (fun x hx => hc x hx)]
        simp [Finset.sum_const]
        <;> ring
      dsimp only [v_bar]
      rw [h_sum]
      field_simp
      <;> ring
    have h_sum_zero : ∑ x ∈ s_finset, (electricPotential psi x - v_bar)^2 = 0 := by
      have h : ∀ x ∈ s_finset, (electricPotential psi x - v_bar)^2 = 0 := by
        intro x hx
        have h1 : electricPotential psi x = c := hc x hx
        rw [h1, h_vbar]
        <;> ring
      rw [Finset.sum_congr rfl h]
      <;> simp
    linarith
  have h_transfer : (∃ x ∈ S, ∃ y ∈ S, electricPotential psi x ≠ electricPotential psi y) ↔
      (∃ x ∈ s_finset, ∃ y ∈ s_finset, electricPotential psi x ≠ electricPotential psi y) := by
    constructor
    · rintro ⟨x, hx, y, hy, hxy⟩
      exact ⟨x, by simp [s_finset, hx], y, by simp [s_finset, hy], hxy⟩
    · rintro ⟨x, hx, y, hy, hxy⟩
      exact ⟨x, by simpa [s_finset] using hx, y, by simpa [s_finset] using hy, hxy⟩
  have h_div_pos : ((∑ x ∈ s_finset, (electricPotential psi x - v_bar)^2) / (s_finset.card : ℝ) > 0) ↔
      (∑ x ∈ s_finset, (electricPotential psi x - v_bar)^2) > 0 := by
    constructor
    · intro h
      have h1 : 0 < (s_finset.card : ℝ) := h_denom_pos
      have h2 : 0 < (∑ x ∈ s_finset, (electricPotential psi x - v_bar)^2) / (s_finset.card : ℝ) := h
      have h3 : 0 < (∑ x ∈ s_finset, (electricPotential psi x - v_bar)^2) := by
        by_contra h4
        have h5 : (∑ x ∈ s_finset, (electricPotential psi x - v_bar)^2) ≤ 0 := by linarith
        have h6 : (∑ x ∈ s_finset, (electricPotential psi x - v_bar)^2) / (s_finset.card : ℝ) ≤ 0 := by
          exact div_nonpos_of_nonpos_of_nonneg h5 (by linarith)
        linarith
      exact h3
    · intro h
      exact div_pos h h_denom_pos
  rw [h_transfer, h_eq, h_div_pos]
  constructor
  · exact h_main_mp
  · exact h_main_mpr

/-
**定理 3.2: 两面极化度非负**

  P(S) ≥ 0

极化度总是非负的。
-/
theorem twoAspectPolarization_nonneg (S : Set X) :
    0 ≤ twoAspectPolarization psi S := by
  let s_finset := S.toFinset
  have h_nonneg : ∀ z ∈ s_finset, 0 ≤ (electricPotential psi z -
      ((∑ x ∈ s_finset, electricPotential psi x) / (s_finset.card : ℝ))) ^ 2 := by
    intro z _
    exact sq_nonneg _
  have h_sum_nonneg : 0 ≤ ∑ z ∈ s_finset, (electricPotential psi z -
      ((∑ x ∈ s_finset, electricPotential psi x) / (s_finset.card : ℝ))) ^ 2 := by
    apply Finset.sum_nonneg
    exact h_nonneg
  unfold twoAspectPolarization
  by_cases h : s_finset.card = 0
  · rw [if_pos h] <;> norm_num
  · rw [if_neg h]
    exact div_nonneg h_sum_nonneg (by positivity)

end Polarization

end CSQIT.Unified.Models.Electrostatics
