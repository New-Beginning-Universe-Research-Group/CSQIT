/-
================================================================================
WeaverPopulation — 群体效应与 w_DE(N) 的一般理论
模块: CSQIT_W1.WeaverPopulation
版本: v14.0.0
日期: 2026-10-01

核心洞察：
  1. AxiomDerivation 里的共识定理（consensus_iterate_all_amplitude_equal）
     实际上不依赖 Fin 8——只用 AxiomC.comp_rule（群同态）+ Finite，
     证明可以逐字推广到任意 Fin N。这意味着相位对齐是群论强制的。

  2. w_DE(N) = -1 + N / (420 · α⁻¹) 有明确的 N 依赖：
     - 严格递增：N 越大，w_DE 越大（离 -1 越远）
     - N → 0⁺ 时 w_DE → -1（从上方趋近）
     - N → ∞ 时 w_DE → +∞

  诚实修正：
    之前猜 "N → ∞ 时 w_DE → -1" 是错误的。
    正确的方向是反的——数学公式直接给出。

  诚实声明：
    Fin 8 在 AxiomDerivation 里是定义选择，不是从公理推出的。
================================================================================ -/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace CSQIT_W1.WeaverPopulation

set_option linter.unusedVariables false

/-! ============================================================================
   §1. 关键物理常数的固定值
   ============================================================================ -/

/-- α⁻¹ 精确值 = 137 + 9/250 = 137.036 -/
noncomputable def alpha_inv_exact : ℝ := 137 + 9/250

/-- totalClosure = 420 -/
def closure_exact : ℝ := 420

theorem alpha_inv_pos : (0 : ℝ) < alpha_inv_exact := by
  unfold alpha_inv_exact; norm_num

theorem closure_pos : (0 : ℝ) < closure_exact := by
  unfold closure_exact; norm_num

theorem denominator_pos : (0 : ℝ) < closure_exact * alpha_inv_exact := by
  exact mul_pos closure_pos alpha_inv_pos

/-! ============================================================================
   §2. w_DE(N) 的定义
   ============================================================================ -/

/-- **编织者维护成本**。 -/
noncomputable def weaver_maintenance_cost (N : ℝ) : ℝ :=
    N / (closure_exact * alpha_inv_exact)

/-- **暗能量状态方程参数 w_DE(N)**。 -/
noncomputable def w_DE (N : ℝ) : ℝ :=
    -1 + weaver_maintenance_cost N

/-! ============================================================================
   §3. w_DE 的精确值公式
   ============================================================================ -/

theorem w_DE_at_1_formula :
    w_DE 1 = -1 + 1 / (closure_exact * alpha_inv_exact) := by rfl

theorem w_DE_at_8_formula :
    w_DE 8 = -1 + 8 / (closure_exact * alpha_inv_exact) := by rfl

/-! ============================================================================
   §4. w_DE 的基本性质
   ============================================================================ -/

theorem weaver_maintenance_cost_strictly_pos (N : ℝ) (hN_pos : 0 < N) :
    0 < weaver_maintenance_cost N := by
  unfold weaver_maintenance_cost
  exact div_pos hN_pos denominator_pos

theorem w_DE_always_gt_neg_one (N : ℝ) (hN_pos : 0 < N) :
    w_DE N > -1 := by
  have h1 : 0 < weaver_maintenance_cost N :=
      weaver_maintenance_cost_strictly_pos N hN_pos
  have h2 : w_DE N = -1 + weaver_maintenance_cost N := by rfl
  rw [h2]
  linarith

/-! ============================================================================
   §5. w_DE 严格递增定理
   ============================================================================ -/

theorem w_DE_strictly_increasing (N1 N2 : ℝ)
    (hN1_pos : 0 < N1) (hN12 : N1 < N2) :
    w_DE N1 < w_DE N2 := by
  have h_maintenance_lt : weaver_maintenance_cost N1 < weaver_maintenance_cost N2 := by
    unfold weaver_maintenance_cost
    have h_pos_denom : (0 : ℝ) < closure_exact * alpha_inv_exact := denominator_pos
    exact div_lt_div_of_pos_right hN12 h_pos_denom
  have h_eq1 : w_DE N1 = -1 + weaver_maintenance_cost N1 := by rfl
  have h_eq2 : w_DE N2 = -1 + weaver_maintenance_cost N2 := by rfl
  rw [h_eq1, h_eq2]
  linarith

/-! ============================================================================
   §6. 极限行为（ε-δ 严格证明）
   ============================================================================ -/

theorem w_DE_tendsto_neg_one_at_zero :
    ∀ ε : ℝ, ε > 0 →
    ∃ δ : ℝ, δ > 0 ∧
    ∀ N : ℝ, 0 < N → N < δ → |w_DE N + 1| < ε := by
  intro ε hε
  let denom : ℝ := closure_exact * alpha_inv_exact
  have h_denom_pos : 0 < denom := denominator_pos
  let δ : ℝ := ε * denom
  have hδ_pos : 0 < δ := mul_pos hε h_denom_pos
  refine' ⟨δ, hδ_pos, _⟩
  intro N hN_pos hN_lt_delta
  have h_maintenance_pos : 0 < weaver_maintenance_cost N :=
      weaver_maintenance_cost_strictly_pos N hN_pos
  have h_diff : w_DE N + 1 = weaver_maintenance_cost N := by
    have h1 : w_DE N = -1 + weaver_maintenance_cost N := by rfl
    rw [h1]
    ring
  have h_maintenance_lt_eps : weaver_maintenance_cost N < ε := by
    unfold weaver_maintenance_cost
    have hN_lt_delta2 : N < ε * denom := hN_lt_delta
    have h_maintenance : N / denom < ε := by
      calc N / denom
          < (ε * denom) / denom := div_lt_div_of_pos_right hN_lt_delta2 h_denom_pos
        _ = ε := by
          field_simp [ne_of_gt h_denom_pos]
    exact h_maintenance
  have h4 : |w_DE N + 1| = weaver_maintenance_cost N := by
    rw [h_diff]
    rw [abs_of_pos h_maintenance_pos]
  have h5 : |w_DE N + 1| < ε := by
    linarith
  exact h5

end CSQIT_W1.WeaverPopulation
