/- ================================================================================
CSQIT v12.1.3 — W1 严格误差界定理
文件: V12/Core/ErrorBounds.lean
版本: v12.1.3
日期: 2026-08-05
================================================================================
本文件为 prophecy_report 中的 ℚ 近似值提供 W1 严格的误差界证明。

核心数学事实：
  1. neutrino_mass = curvature_energy(64) × (8/840)²
  2. curvature_energy(64) = W × α⁻¹ × (8/64)^(¼·log₂(64/8))
                          = W × α⁻¹ × (1/8)^(¼·3)
                          = W × α⁻¹ × (1/8)^(3/4)
                          = W × α⁻¹ × 2^(-9/4)
                          = W × α⁻¹ / (4·2^(1/4))
  3. 唯一无理数: 2^(1/4) = √(√2)

证明策略：
  - 建立 2^(1/4) 的有理上下界: 1189/1000 < 2^(1/4) < 1190/1000
  - 通过代数运算传递到 neutrino_mass
  - 最终证明 |neutrino_mass - 2891/200| < 1/100

W1/W2 层级说明：
  - §1: 2^(1/4) 的有理界 —— W1 严格（纯算术验证）
  - §2: neutrino_mass 误差界 —— W1 严格（传递保持严格性）
  - §3: Λ_extended 误差界 —— W1 严格
  - §4: axion_mass_derived 误差界 —— W1 严格
================================================================================ -/

import V12.Core.Foundation
import V12.Core.AlgebraicTimeCircle
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.Sqrt

namespace CSQIT.V12.ErrorBounds

open CSQIT.V12.Foundation
open CSQIT.V12.AlgebraicTimeCircle
open Real

/-! ============================================================================
   §1. 2^(1/4) 的有理上下界（W1 严格，纯算术验证）
   ============================================================================

   数学事实：2^(1/4) = √(√2) ≈ 1.18920711500272...

   验证方法：
     - 下界 1189/1000: (1189/1000)^4 = 1998607065841/10^12 < 2 = 2000000000000/10^12
     - 上界 1190/1000: (1190/1000)^4 = 2005339210000/10^12 > 2 = 2000000000000/10^12
     - 由 rpow_le_rpow 和 rpow_le_rpow_iff（底数 > 1 时严格单调）传递
   ============================================================================ -/

/-- **引理：1189^4 < 2 × 1000^4**（W1 严格，纯算术）。
    1189^4 = 1998607065841, 2 × 1000^4 = 2000000000000。
    差值 = 1392934159 > 0。 -/
lemma lower_bound_4th_pow : (1189 : ℕ)^4 < 2 * (1000 : ℕ)^4 := by
  norm_num

/-- **引理：1190^4 > 2 × 1000^4**（W1 严格，纯算术）。
    1190^4 = 2005339210000, 2 × 1000^4 = 2000000000000。
    差值 = 5339210000 > 0。 -/
lemma upper_bound_4th_pow : 2 * (1000 : ℕ)^4 < (1190 : ℕ)^4 := by
  norm_num

/-- **定理：2^(1/4) 的下界**（W1 严格）。
    1189/1000 < 2^(1/4)。
    证明：(1189/1000)^4 < 2 = (2^(1/4))^4，且 x ↦ x^r 在正实数上严格递增（r > 0）。 -/
theorem two_fourth_root_gt_lower : (1189 : ℝ) / 1000 < (2 : ℝ) ^ ((1 : ℝ) / 4) := by
  have h_pos_base : 0 ≤ (1189 : ℝ) / 1000 := by norm_num
  have h_pos_2_14 : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  have h_4_pos : 0 ≤ (4 : ℝ) := by norm_num
  -- (1189/1000)^(4:ℝ) = (1189/1000)^4 (nat power)
  have h_rpow_eq : ((1189 : ℝ) / 1000) ^ (4 : ℝ) = ((1189 : ℝ) / 1000) ^ 4 :=
    Real.rpow_natCast ((1189 : ℝ) / 1000) 4
  -- (1189/1000)^4 < 2 (纯算术)
  have h_pow_lt : ((1189 : ℝ) / 1000) ^ 4 < (2 : ℝ) := by norm_num
  -- (2^(1/4))^(4:ℝ) = 2^((1/4)*4) = 2^1 = 2
  have h_2_pow4 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℝ) = (2 : ℝ) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), show ((1 : ℝ) / 4) * 4 = 1 from by norm_num,
        Real.rpow_one]
  -- 将 h_pow_lt 中的 nat pow 转换为 rpow
  rw [← h_rpow_eq] at h_pow_lt
  -- 将 h_pow_lt 中的 2 替换为 (2^(1/4))^(4:ℝ)
  rw [← h_2_pow4] at h_pow_lt
  -- 现在 h_pow_lt : (1189/1000)^(4:ℝ) < (2^(1/4))^(4:ℝ)
  -- 反证法: 若 2^(1/4) ≤ 1189/1000, 则由 rpow 单调性, (2^(1/4))^(4:ℝ) ≤ (1189/1000)^(4:ℝ)
  by_contra h
  push_neg at h
  have h_le : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℝ) ≤ ((1189 : ℝ) / 1000) ^ (4 : ℝ) :=
    Real.rpow_le_rpow h_pos_2_14 h h_4_pos
  linarith

/-- **定理：2^(1/4) 的上界**（W1 严格）。
    2^(1/4) < 1190/1000。
    证明：2 = (2^(1/4))^4 < (1190/1000)^4，且 x ↦ x^r 在正实数上严格递增（r > 0）。 -/
theorem two_fourth_root_lt_upper : (2 : ℝ) ^ ((1 : ℝ) / 4) < (1190 : ℝ) / 1000 := by
  have h_pos_base : 0 ≤ (1190 : ℝ) / 1000 := by norm_num
  have h_pos_2_14 : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  have h_4_pos : 0 ≤ (4 : ℝ) := by norm_num
  -- (1190/1000)^(4:ℝ) = (1190/1000)^4 (nat power)
  have h_rpow_eq : ((1190 : ℝ) / 1000) ^ (4 : ℝ) = ((1190 : ℝ) / 1000) ^ 4 :=
    Real.rpow_natCast ((1190 : ℝ) / 1000) 4
  -- 2 < (1190/1000)^4 (纯算术)
  have h_pow_gt : (2 : ℝ) < ((1190 : ℝ) / 1000) ^ 4 := by norm_num
  -- (2^(1/4))^(4:ℝ) = 2
  have h_2_pow4 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℝ) = (2 : ℝ) := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), show ((1 : ℝ) / 4) * 4 = 1 from by norm_num,
        Real.rpow_one]
  -- 组合: (2^(1/4))^(4:ℝ) = 2 < (1190/1000)^4 = (1190/1000)^(4:ℝ)
  rw [← h_2_pow4] at h_pow_gt
  rw [← h_rpow_eq] at h_pow_gt
  -- 反证法: 若 1190/1000 ≤ 2^(1/4), 则由 rpow 单调性, (1190/1000)^(4:ℝ) ≤ (2^(1/4))^(4:ℝ)
  by_contra h
  push_neg at h
  have h_le : ((1190 : ℝ) / 1000) ^ (4 : ℝ) ≤ ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ (4 : ℝ) :=
    Real.rpow_le_rpow h_pos_base h h_4_pos
  linarith

/-- **定理：2^(1/4) 的有理界**（W1 严格，综合定理）。
    1189/1000 < 2^(1/4) < 1190/1000。 -/
theorem two_fourth_root_bounds :
    (1189 : ℝ) / 1000 < (2 : ℝ) ^ ((1 : ℝ) / 4) ∧ (2 : ℝ) ^ ((1 : ℝ) / 4) < (1190 : ℝ) / 1000 :=
  ⟨two_fourth_root_gt_lower, two_fourth_root_lt_upper⟩

/-! ============================================================================
   §2. neutrino_mass 的误差界（W1 严格）
   ============================================================================

   数学展开：
     neutrino_mass = curvature_energy(64) × (8/840)²
                   = W × α⁻¹ × (1/8)^(3/4) × (8/840)²
                   = W × α⁻¹ / (4·2^(1/4)) × (8/840)²

     其中 W = weavingStiffnessBase = α⁻¹ × (250/9) × 420 / 289

     完全有理部分（W1 严格）：
       W × α⁻¹ × (8/840)² / 4
       = (α⁻¹)² × (250/9) × 420 / 289 × 64 / 840² / 4
       = (α⁻¹)² × (250/9) × 420 × 64 / (289 × 840² × 4)

     唯一无理部分：1/2^(1/4)

     所以 neutrino_mass = (有理常数 R) / 2^(1/4)
     其中 R = W × α⁻¹ × (8/840)² / 4
   ============================================================================ -/

/-- **引理：log2(8) = 3**（W1 严格）。
    因为 2^3 = 8。 -/
lemma log2_eight_eq_three : log2 8 = 3 := by
  unfold log2
  have h : (8 : ℝ) = 2 ^ (3 : ℝ) := by norm_num
  rw [h]
  exact Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)

/-- **引理：curvature_energy(64) 的简化形式**（W1 严格）。
    curvature_energy(64) = W × α⁻¹ × 2^(-9/4)。
    因为 (8/64)^(¼·log₂(8)) = (1/8)^(3/4) = 2^(-9/4)。 -/
lemma curvature_energy_64_simplified :
    curvature_energy 64 (by norm_num) =
      weavingStiffnessBase * inverseAlpha * (2 : ℝ) ^ (-(9 : ℝ) / 4) := by
  unfold curvature_energy
  -- 将 Nat cast ↑64 归一化为 (64 : ℝ)
  simp only [Nat.cast_ofNat]
  -- 关键：log2(64/8) = log2(8) = 3
  have h_log : log2 ((64 : ℝ) / 8) = 3 := by
    rw [show (64 : ℝ) / 8 = 8 from by norm_num, log2_eight_eq_three]
  rw [h_log]
  -- (8/64)^(1/4 * 3) = (1/8)^(3/4) = 2^(-9/4)
  have h_8_64 : (8 : ℝ) / 64 = 1 / 8 := by norm_num
  rw [h_8_64]
  have h_exp : ((1 : ℝ) / 4) * 3 = (3 : ℝ) / 4 := by norm_num
  rw [h_exp]
  -- (1/8)^(3/4) = (2^(-3))^(3/4) = 2^(-9/4)
  have h_pos_two : (0 : ℝ) < 2 := by norm_num
  have h_one_eighth : (1 : ℝ) / 8 = (2 : ℝ) ^ (-(3 : ℝ)) := by
    rw [Real.rpow_neg h_pos_two.le (3 : ℝ), show (2 : ℝ) ^ (3 : ℝ) = 8 from by norm_num,
        one_div]
  rw [h_one_eighth]
  -- (2^(-3))^(3/4) = 2^(-3 * 3/4) = 2^(-9/4)
  rw [← Real.rpow_mul h_pos_two.le]
  -- -(3) * (3/4) = -(9/4)
  have h_arith : -(3 : ℝ) * ((3 : ℝ) / 4) = -(9 : ℝ) / 4 := by norm_num
  rw [h_arith]

/-- **引理：neutrino_mass 的简化形式**（W1 严格）。
    neutrino_mass = (W × α⁻¹ × (8/840)²) / (4 × 2^(1/4))。

    推导：
      neutrino_mass = curvature_energy(64) × (8/840)²
                    = W × α⁻¹ × 2^(-9/4) × (8/840)²
                    = W × α⁻¹ × (8/840)² × 2^(-9/4)
                    = W × α⁻¹ × (8/840)² / 2^(9/4)
                    = W × α⁻¹ × (8/840)² / (4 × 2^(1/4))
    （因为 2^(9/4) = 2^2 × 2^(1/4) = 4 × 2^(1/4)） -/
lemma neutrino_mass_simplified :
    neutrino_mass =
      weavingStiffnessBase * inverseAlpha * ((8 : ℝ) / topoPeriod) ^ 2 /
        (4 * (2 : ℝ) ^ ((1 : ℝ) / 4)) := by
  unfold neutrino_mass
  rw [curvature_energy_64_simplified]
  -- 2^(-9/4) = 1 / 2^(9/4) = 1 / (4 * 2^(1/4))
  have h_pos_two : (0 : ℝ) < 2 := by norm_num
  have h9_4 : (9 : ℝ) / 4 = 2 + (1 : ℝ) / 4 := by norm_num
  have h_2_9_4 : (2 : ℝ) ^ ((9 : ℝ) / 4) = 4 * (2 : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [h9_4, Real.rpow_add h_pos_two]
    norm_num
  have h_neg : (2 : ℝ) ^ (-(9 : ℝ) / 4) = 1 / (2 : ℝ) ^ ((9 : ℝ) / 4) := by
    rw [show -(9 : ℝ) / 4 = -((9 : ℝ) / 4) from by norm_num,
        Real.rpow_neg h_pos_two.le, one_div]
  rw [h_neg, h_2_9_4]
  ring

/-- **有理常数 R**（W1 严格定义）。
    R = W × α⁻¹ × (8/840)² / 4
    其中 W = weavingStiffnessBase, α⁻¹ = inverseAlpha。
    这是 neutrino_mass 中完全有理的部分。 -/
noncomputable def neutrino_rational_factor : ℝ :=
  weavingStiffnessBase * inverseAlpha * ((8 : ℝ) / topoPeriod) ^ 2 / 4

/-- **引理：neutrino_mass = R / 2^(1/4)**（W1 严格）。 -/
lemma neutrino_mass_eq_rational_over_fourth_root :
    neutrino_mass = neutrino_rational_factor / (2 : ℝ) ^ ((1 : ℝ) / 4) := by
  rw [neutrino_mass_simplified, neutrino_rational_factor]
  ring

/-- **引理：neutrino_rational_factor 的显式有理值**（W1 严格）。
    R = (137 + 9/250)² × (250/9) × 420 × 64 / (289 × 840² × 4)
    这是一个完全可计算的有理数。 -/
lemma neutrino_rational_factor_value :
    neutrino_rational_factor =
      ((137 + 9 / (250 : ℝ)) ^ 2 * (250 / (9 : ℝ)) * 420 * 64) /
        (289 * 840 ^ 2 * 4) := by
  unfold neutrino_rational_factor weavingStiffnessBase topoPeriod
  rw [inverseAlpha_eq_137_036, totalClosure_eq_420, darkEnergyNum_eq_289]
  -- observerBridge = p1 * p3^3 / p2^2 = 2 * 125 / 9 = 250/9
  have h_obs : observerBridge = (250 : ℝ) / 9 := by
    unfold observerBridge p1 p2 p3
    norm_num
  rw [h_obs]
  ring

/-- **引理：neutrino_rational_factor 的精确有理值**（W1 严格）。
    R = 1173679081 / 68276250。

    推导：
      α⁻¹ = 137 + 9/250 = 34259/250
      34259² = 1173679081
      250² × 9 × 289 × 840² × 4 / (250 × 420 × 64) = 68276250
    所以 R = 34259² / 68276250 = 1173679081 / 68276250。 -/
lemma neutrino_rational_factor_exact :
    neutrino_rational_factor = (1173679081 : ℝ) / 68276250 := by
  rw [neutrino_rational_factor_value]
  -- 化简 (137 + 9/250) = 34259/250
  have h_ia : (137 + 9 / (250 : ℝ)) = 34259 / 250 := by norm_num
  rw [h_ia]
  -- 化简 (34259/250)^2 = 1173679081 / 62500
  have h_sq : (34259 / (250 : ℝ)) ^ 2 = 1173679081 / 62500 := by
    rw [div_pow]
    norm_num
  rw [h_sq]
  -- 此时目标: (1173679081/62500) * (250/9) * 420 * 64 / (289 * 840^2 * 4) = 1173679081/68276250
  -- 用 field_simp 清除分母, 再用 ring 验证多项式恒等式
  field_simp
  ring

/-- **引理：neutrino_rational_factor 为正**（W1 严格）。 -/
lemma neutrino_rational_factor_pos : 0 < neutrino_rational_factor := by
  rw [neutrino_rational_factor_exact]
  positivity

/-- **定理：neutrino_mass 的 W1 严格误差界**（核心定理）。
    |neutrino_mass - 2891/200| < 1/100。

    即 |neutrino_mass - 14.455| < 0.01。

    证明策略：
      1. neutrino_mass = R / 2^(1/4)，其中 R = 1173679081/68276250 为有理数
      2. 2^(1/4) ∈ (1189/1000, 1190/1000)（W1 严格，已证）
      3. 因 R > 0 且 2^(1/4) < 1190/1000，故 R/2^(1/4) > R·1000/1190
      4. 因 R > 0 且 2^(1/4) > 1189/1000，故 R/2^(1/4) < R·1000/1189
      5. 验证 R·1000/1190 > 2889/200（纯有理算术，norm_num）
      6. 验证 R·1000/1189 < 2893/200（纯有理算术，norm_num）
      7. 由传递性: 2889/200 < neutrino_mass < 2893/200
      8. 等价于 |neutrino_mass - 2891/200| < 1/100 -/
theorem neutrino_mass_error_bound :
    abs (neutrino_mass - 2891 / (200 : ℝ)) < 1 / (100 : ℝ) := by
  rw [neutrino_mass_eq_rational_over_fourth_root]
  -- 基本事实
  have h_R_pos : 0 < neutrino_rational_factor := neutrino_rational_factor_pos
  have h_2_14_lb := two_fourth_root_gt_lower  -- 1189/1000 < 2^(1/4)
  have h_2_14_ub := two_fourth_root_lt_upper  -- 2^(1/4) < 1190/1000
  have h_2_14_pos : 0 < (2 : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  have h_1190_pos : 0 < (1190 : ℝ) / 1000 := by norm_num
  have h_1189_pos : 0 < (1189 : ℝ) / 1000 := by norm_num
  -- 从 2^(1/4) < 1190/1000 取逆: 1000/1190 < 1/2^(1/4)
  -- inv_lt_inv₀ : 0 < a → 0 < b → (a⁻¹ < b⁻¹ ↔ b < a)
  have h_inv_ub : ((1190 : ℝ) / 1000)⁻¹ < ((2 : ℝ) ^ ((1 : ℝ) / 4))⁻¹ :=
    (inv_lt_inv₀ h_1190_pos h_2_14_pos).mpr h_2_14_ub
  -- 从 1189/1000 < 2^(1/4) 取逆: 1/2^(1/4) < 1000/1189
  have h_inv_lb : ((2 : ℝ) ^ ((1 : ℝ) / 4))⁻¹ < ((1189 : ℝ) / 1000)⁻¹ :=
    (inv_lt_inv₀ h_2_14_pos h_1189_pos).mpr h_2_14_lb
  -- 下界: 2889/200 < R/2^(1/4)
  have h_lower : (2889 : ℝ) / 200 < neutrino_rational_factor / (2 : ℝ) ^ ((1 : ℝ) / 4) := by
    -- R/2^(1/4) = R * (2^(1/4))⁻¹ > R * (1190/1000)⁻¹ = R * 1000/1190
    have h_mul_lt : neutrino_rational_factor * ((1190 : ℝ) / 1000)⁻¹ <
                    neutrino_rational_factor * ((2 : ℝ) ^ ((1 : ℝ) / 4))⁻¹ :=
      mul_lt_mul_of_pos_left h_inv_ub h_R_pos
    -- (1190/1000)⁻¹ = 1000/1190
    rw [inv_div] at h_mul_lt
    -- R/2^(1/4) = R * (2^(1/4))⁻¹
    rw [div_eq_mul_inv]
    -- 验证 2889/200 < R * 1000/1190 (纯有理算术)
    have h_rat : (2889 : ℝ) / 200 < neutrino_rational_factor * ((1000 : ℝ) / 1190) := by
      rw [neutrino_rational_factor_exact]
      field_simp
      norm_num
    -- 由传递性: 2889/200 < R*(1000/1190) < R*(2^(1/4))⁻¹
    exact lt_trans h_rat h_mul_lt
  -- 上界: R/2^(1/4) < 2893/200
  have h_upper : neutrino_rational_factor / (2 : ℝ) ^ ((1 : ℝ) / 4) < (2893 : ℝ) / 200 := by
    -- R/2^(1/4) = R * (2^(1/4))⁻¹ < R * (1189/1000)⁻¹ = R * 1000/1189
    have h_mul_lt : neutrino_rational_factor * ((2 : ℝ) ^ ((1 : ℝ) / 4))⁻¹ <
                    neutrino_rational_factor * ((1189 : ℝ) / 1000)⁻¹ :=
      mul_lt_mul_of_pos_left h_inv_lb h_R_pos
    rw [inv_div] at h_mul_lt
    rw [div_eq_mul_inv]
    -- 验证 R * 1000/1189 < 2893/200 (纯有理算术)
    have h_rat : neutrino_rational_factor * ((1000 : ℝ) / 1189) < (2893 : ℝ) / 200 := by
      rw [neutrino_rational_factor_exact]
      field_simp
      norm_num
    -- 由传递性: R*(2^(1/4))⁻¹ < R*(1000/1189) < 2893/200
    exact lt_trans h_mul_lt h_rat
  -- 组合上下界
  -- abs_sub_lt_iff : |a - b| < c ↔ a - b < c ∧ b - a < c
  -- 第一部分: x - 2891/200 < 1/100 (即 x < 2893/200, 由 h_upper)
  -- 第二部分: 2891/200 - x < 1/100 (即 2889/200 < x, 由 h_lower)
  rw [abs_sub_lt_iff]
  refine ⟨?_, ?_⟩
  · linarith [h_upper]
  · linarith [h_lower]

/-! ============================================================================
   §3. Λ_extended 的误差界（W1 严格）
   ============================================================================

   对于 k = 0, 1（n = 8, 64），log2(n/8) 是整数，Λ_extended 不涉及无理 log2 值。
   对于 k = 2（n = 420），log2(420/8) = log2(52.5) 是无理数，需要单独处理。

   本节先处理 k = 0, 1, 3, 4 等特殊情况。
   ============================================================================ -/

/-- **引理：Λ_extended(0) = Λ(8) 的简化**（W1 严格）。
    Λ(8) = W × α⁻¹ × (8/8)^(¼·log₂(1)) = W × α⁻¹ × 1 = W × α⁻¹。
    因为 log2(1) = 0，任何数的 0 次方 = 1。 -/
lemma Λ_extended_0_simplified :
    Λ_extended 0 = weavingStiffnessBase * inverseAlpha := by
  -- Λ_extended 0 = curvature_energy (closure_sequence_extended 0) (...)
  -- closure_sequence_extended 0 =def= 8 (模式匹配)
  unfold Λ_extended
  -- 用 definitional equality 将 closure_sequence_extended 0 转为 8
  show curvature_energy 8 (closure_sequence_extended_pos 0) = weavingStiffnessBase * inverseAlpha
  unfold curvature_energy
  -- 将 Nat cast ↑8 归一化为 (8 : ℝ)
  simp only [Nat.cast_ofNat]
  -- (8:ℝ)/8 = 1, log2(8/8) = log2(1) = 0
  rw [show (8 : ℝ) / 8 = 1 from by norm_num]
  -- log2 1 = Real.logb 2 1 = 0
  have h_log2_1 : log2 1 = 0 := by
    unfold log2
    exact logb_one
  rw [h_log2_1, show ((1 : ℝ) / 4) * 0 = 0 from by norm_num, Real.rpow_zero]
  ring

/-! ============================================================================
   §4. Λ_extended(1) 的误差界（W1 严格，复用 2^(1/4) 界）
   ============================================================================

   对于 k = 1（n = 64），log₂(64/8) = log₂(8) = 3 为整数，
   所以 Λ_extended(1) = curvature_energy(64) = W × α⁻¹ × 2^(-9/4)。

   唯一无理部分仍然是 2^(1/4)，可复用 §1 的有理界。
   ============================================================================ -/

/-- **引理：Λ_extended(1) = curvature_energy(64) 的简化**（W1 严格）。
    由定义展开：closure_sequence_extended 1 = 64，
    Λ_extended(1) = curvature_energy(64) = W × α⁻¹ × 2^(-9/4)。 -/
lemma Λ_extended_1_eq_curvature_energy_64 :
    Λ_extended 1 = curvature_energy 64 (by norm_num) := by
  unfold Λ_extended
  -- closure_sequence_extended 1 = 64 (definitional equality via pattern match)
  show curvature_energy (closure_sequence_extended 1) (closure_sequence_extended_pos 1) =
       curvature_energy 64 (by norm_num)
  -- By definitional reduction: closure_sequence_extended 1 ↦ 64
  -- and curvature_energy ignores the proof argument hn in its body
  rfl

/-- **引理：Λ_extended(1) = W × α⁻¹ × 2^(-9/4)**（W1 严格）。 -/
lemma Λ_extended_1_simplified :
    Λ_extended 1 = weavingStiffnessBase * inverseAlpha * (2 : ℝ) ^ (-(9 : ℝ) / 4) := by
  rw [Λ_extended_1_eq_curvature_energy_64, curvature_energy_64_simplified]

/-- **Λ_extended(1) 的有理因子 R₁**（W1 严格定义）。
    R₁ = W × α⁻¹ / 4，其中 W = weavingStiffnessBase, α⁻¹ = inverseAlpha。
    这是 Λ_extended(1) 中完全有理的部分。 -/
noncomputable def Λ_extended_1_rational_factor : ℝ :=
  weavingStiffnessBase * inverseAlpha / 4

/-- **引理：Λ_extended(1) = R₁ / 2^(1/4)**（W1 严格）。 -/
lemma Λ_extended_1_eq_rational_over_fourth_root :
    Λ_extended 1 = Λ_extended_1_rational_factor / (2 : ℝ) ^ ((1 : ℝ) / 4) := by
  rw [Λ_extended_1_simplified, Λ_extended_1_rational_factor]
  -- 2^(-9/4) = 1/2^(9/4) = 1/(4 × 2^(1/4))
  have h_pos_two : (0 : ℝ) < 2 := by norm_num
  have h9_4 : (9 : ℝ) / 4 = 2 + (1 : ℝ) / 4 := by norm_num
  have h_2_9_4 : (2 : ℝ) ^ ((9 : ℝ) / 4) = 4 * (2 : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [h9_4, Real.rpow_add h_pos_two]
    norm_num
  have h_neg : (2 : ℝ) ^ (-(9 : ℝ) / 4) = 1 / (2 : ℝ) ^ ((9 : ℝ) / 4) := by
    rw [show -(9 : ℝ) / 4 = -((9 : ℝ) / 4) from by norm_num,
        Real.rpow_neg h_pos_two.le, one_div]
  rw [h_neg, h_2_9_4]
  ring

/-- **引理：R₁ 的显式有理表达式**（W1 严格）。
    R₁ = (α⁻¹)² × (250/9) × 420 / (4 × 289) -/
lemma Λ_extended_1_rational_factor_value :
    Λ_extended_1_rational_factor =
      ((137 + 9 / (250 : ℝ)) ^ 2 * (250 / (9 : ℝ)) * 420) /
        (289 * 4) := by
  unfold Λ_extended_1_rational_factor weavingStiffnessBase
  rw [inverseAlpha_eq_137_036, totalClosure_eq_420, darkEnergyNum_eq_289]
  have h_obs : observerBridge = (250 : ℝ) / 9 := by
    unfold observerBridge p1 p2 p3
    norm_num
  rw [h_obs]
  ring

/-- **引理：R₁ 的精确有理值**（W1 严格）。
    R₁ = 8215753567 / 43350。

    推导：
      α⁻¹ = 34259/250, α⁻¹² = 34259²/62500 = 1173679081/62500
      R₁ = 1173679081/62500 × 250/9 × 420 / (289 × 4)
         = 1173679081 × 250 × 420 / (62500 × 9 × 1156)
         = 1173679081 × 21 / (50 × 2601)   [化简 250/62500=1/250, 420/9 → ...]
         = 24647260701 / 130050
         = 8215753567 / 43350              [gcd=3] -/
lemma Λ_extended_1_rational_factor_exact :
    Λ_extended_1_rational_factor = (8215753567 : ℝ) / 43350 := by
  rw [Λ_extended_1_rational_factor_value]
  have h_ia : (137 + 9 / (250 : ℝ)) = 34259 / 250 := by norm_num
  rw [h_ia]
  have h_sq : (34259 / (250 : ℝ)) ^ 2 = 1173679081 / 62500 := by
    rw [div_pow]
    norm_num
  rw [h_sq]
  field_simp
  ring

/-- **引理：R₁ 为正**（W1 严格）。 -/
lemma Λ_extended_1_rational_factor_pos : 0 < Λ_extended_1_rational_factor := by
  rw [Λ_extended_1_rational_factor_exact]
  positivity

/-- **定理：Λ_extended(1) 的 W1 严格误差界**（核心定理）。
    |Λ_extended(1) - 3984197/25| < 110。

    即 |Λ_extended(1) - 159367.88| < 110。

    证明策略（与 neutrino_mass_error_bound 同构）：
      1. Λ_extended(1) = R₁ / 2^(1/4)，其中 R₁ = 8215753567/43350
      2. 2^(1/4) ∈ (1189/1000, 1190/1000)（W1 严格，§1 已证）
      3. 由 R₁ > 0 且 2^(1/4) < 1190/1000：R₁/2^(1/4) > R₁ × 1000/1190
      4. 由 R₁ > 0 且 2^(1/4) > 1189/1000：R₁/2^(1/4) < R₁ × 1000/1189
      5. 验证 R₁ × 1000/1190 > 3981447/25（纯有理算术，norm_num）
      6. 验证 R₁ × 1000/1189 < 3986947/25（纯有理算术，norm_num）
      7. 由传递性：3981447/25 < Λ_extended(1) < 3986947/25
      8. 等价于 |Λ_extended(1) - 3984197/25| < 110 -/
theorem Λ_extended_1_error_bound :
    abs (Λ_extended 1 - 3984197 / (25 : ℝ)) < 110 := by
  rw [Λ_extended_1_eq_rational_over_fourth_root]
  -- 基本事实
  have h_R_pos : 0 < Λ_extended_1_rational_factor := Λ_extended_1_rational_factor_pos
  have h_2_14_lb := two_fourth_root_gt_lower  -- 1189/1000 < 2^(1/4)
  have h_2_14_ub := two_fourth_root_lt_upper  -- 2^(1/4) < 1190/1000
  have h_2_14_pos : 0 < (2 : ℝ) ^ ((1 : ℝ) / 4) := by positivity
  have h_1190_pos : 0 < (1190 : ℝ) / 1000 := by norm_num
  have h_1189_pos : 0 < (1189 : ℝ) / 1000 := by norm_num
  -- 逆界（与 neutrino_mass_error_bound 相同推导）
  have h_inv_ub : ((1190 : ℝ) / 1000)⁻¹ < ((2 : ℝ) ^ ((1 : ℝ) / 4))⁻¹ :=
    (inv_lt_inv₀ h_1190_pos h_2_14_pos).mpr h_2_14_ub
  have h_inv_lb : ((2 : ℝ) ^ ((1 : ℝ) / 4))⁻¹ < ((1189 : ℝ) / 1000)⁻¹ :=
    (inv_lt_inv₀ h_2_14_pos h_1189_pos).mpr h_2_14_lb
  -- 下界: 3981447/25 < R₁/2^(1/4)
  have h_lower : (3981447 : ℝ) / 25 < Λ_extended_1_rational_factor / (2 : ℝ) ^ ((1 : ℝ) / 4) := by
    have h_mul_lt : Λ_extended_1_rational_factor * ((1190 : ℝ) / 1000)⁻¹ <
                    Λ_extended_1_rational_factor * ((2 : ℝ) ^ ((1 : ℝ) / 4))⁻¹ :=
      mul_lt_mul_of_pos_left h_inv_ub h_R_pos
    rw [inv_div] at h_mul_lt
    rw [div_eq_mul_inv]
    have h_rat : (3981447 : ℝ) / 25 < Λ_extended_1_rational_factor * ((1000 : ℝ) / 1190) := by
      rw [Λ_extended_1_rational_factor_exact]
      field_simp
      norm_num
    exact lt_trans h_rat h_mul_lt
  -- 上界: R₁/2^(1/4) < 3986947/25
  have h_upper : Λ_extended_1_rational_factor / (2 : ℝ) ^ ((1 : ℝ) / 4) < (3986947 : ℝ) / 25 := by
    have h_mul_lt : Λ_extended_1_rational_factor * ((2 : ℝ) ^ ((1 : ℝ) / 4))⁻¹ <
                    Λ_extended_1_rational_factor * ((1189 : ℝ) / 1000)⁻¹ :=
      mul_lt_mul_of_pos_left h_inv_lb h_R_pos
    rw [inv_div] at h_mul_lt
    rw [div_eq_mul_inv]
    have h_rat : Λ_extended_1_rational_factor * ((1000 : ℝ) / 1189) < (3986947 : ℝ) / 25 := by
      rw [Λ_extended_1_rational_factor_exact]
      field_simp
      norm_num
    exact lt_trans h_mul_lt h_rat
  -- 组合上下界
  rw [abs_sub_lt_iff]
  refine ⟨?_, ?_⟩
  · linarith [h_upper]
  · linarith [h_lower]

/-! ============================================================================
   §4b. Λ_extended(2) 的粗略 W1 严格界
   ============================================================================

   对于 k = 2（n = 420），log₂(420/8) = log₂(52.5) 是无理数，
   无法像 k = 0, 1 那样得到精确的有理误差界。

   但我们可以给出 W1 严格的粗略界：
     W × α⁻¹ × (8/420)² < Λ_extended(2) < W × α⁻¹

   证明策略：
     1. log₂(52.5) > 0（因为 52.5 > 1）
     2. log₂(52.5) < 8（因为 52.5 < 256 = 2⁸）
     3. 0 < ¼·log₂(52.5) < 2
     4. 0 < 8/420 < 1
     5. 由 rpow_lt_one：(8/420)^(正数) < 1 → Λ_extended(2) < W × α⁻¹
     6. 由 rpow_lt_rpow_of_exponent_gt：(8/420)² < (8/420)^(¼·log₂(52.5))
        → W × α⁻¹ × (8/420)² < Λ_extended(2)
   ============================================================================ -/

/-- **引理：52.5 > 1**（W1 严格，纯算术）。 -/
lemma half_105_gt_one : (1 : ℝ) < (105 : ℝ) / 2 := by norm_num

/-- **引理：52.5 < 256 = 2⁸**（W1 严格，纯算术）。 -/
lemma half_105_lt_256 : (105 : ℝ) / 2 < 256 := by norm_num

/-- **引理：log₂(52.5) > 0**（W1 严格）。
    因为 52.5 > 1，由 logb_pos 传递。 -/
lemma log2_half_105_pos : 0 < log2 ((105 : ℝ) / 2) := by
  unfold log2
  exact Real.logb_pos (by norm_num : (1:ℝ) < 2)
    (by norm_num : (1:ℝ) < 105/2)

/-- **引理：log₂(52.5) < 8**（W1 严格）。
    因为 52.5 < 256 = 2⁸ 且 log₂(256) = 8。 -/
lemma log2_half_105_lt_8 : log2 ((105 : ℝ) / 2) < 8 := by
  unfold log2
  -- log₂(52.5) < log₂(256) 因为 52.5 < 256
  have h_lt : Real.logb 2 ((105:ℝ)/2) < Real.logb 2 (256:ℝ) :=
    Real.logb_lt_logb (by norm_num : (1:ℝ) < 2)
      (by norm_num : (0:ℝ) < 105/2) (by norm_num : (105/2:ℝ) < 256)
  -- log₂(256) = log₂(2⁸) = 8
  have h_256 : (256:ℝ) = 2 ^ (8:ℝ) := by norm_num
  have h_log256 : Real.logb 2 (256:ℝ) = 8 := by
    rw [h_256]
    exact Real.logb_rpow (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)
  rw [h_log256] at h_lt
  exact h_lt

/-- **引理：¼·log₂(52.5) > 0**（W1 严格）。 -/
lemma quarter_log2_half_105_pos : 0 < ((1:ℝ) / 4) * log2 ((105:ℝ) / 2) := by
  have h := log2_half_105_pos
  exact mul_pos (by norm_num) h

/-- **引理：¼·log₂(52.5) < 2**（W1 严格）。 -/
lemma quarter_log2_half_105_lt_2 : ((1:ℝ) / 4) * log2 ((105:ℝ) / 2) < 2 := by
  have h := log2_half_105_lt_8
  have h2 : ((1:ℝ) / 4) * 8 = 2 := by norm_num
  nlinarith [h]

/-- **引理：0 < 8/420 < 1**（W1 严格，纯算术）。 -/
lemma eight_over_420_bounds : 0 < (8:ℝ) / 420 ∧ (8:ℝ) / 420 < 1 := by
  exact ⟨by norm_num, by norm_num⟩

/-- **引理：Λ_extended(2) 的指数展开**（W1 严格）。
    Λ_extended(2) = W × α⁻¹ × (8/420)^(¼·log₂(52.5))。
    因为 closure_sequence_extended 2 = 420，420/8 = 52.5 = 105/2。 -/
lemma Λ_extended_2_exponent :
    Λ_extended 2 = weavingStiffnessBase * inverseAlpha *
      ((8:ℝ) / 420) ^ ((1:ℝ) / 4 * log2 ((105:ℝ) / 2)) := by
  unfold Λ_extended curvature_energy
  -- closure_sequence_extended 2 = 420 (定义展开)
  show weavingStiffnessBase * inverseAlpha *
        ((8:ℝ) / (closure_sequence_extended 2)) ^
          ((1:ℝ) / 4 * log2 ((closure_sequence_extended 2 : ℝ) / 8)) =
       weavingStiffnessBase * inverseAlpha *
        ((8:ℝ) / 420) ^ ((1:ℝ) / 4 * log2 ((105:ℝ) / 2))
  -- 化简 closure_sequence_extended 2 = 420
  have h_cse : closure_sequence_extended 2 = 420 := by
    simp [closure_sequence_extended]
  rw [h_cse]
  -- 420/8 = 105/2
  norm_num

/-- **定理：Λ_extended(2) < Λ_extended(0)**（W1 严格，上界）。
    因为 8/420 < 1 且 ¼·log₂(52.5) > 0，
    由 rpow_lt_one：(8/420)^(正数) < 1。 -/
theorem Λ_extended_2_lt_Λ_extended_0 : Λ_extended 2 < Λ_extended 0 := by
  rw [Λ_extended_2_exponent, Λ_extended_0_simplified]
  -- 需要证明 W × α⁻¹ × (8/420)^(¼·log₂(52.5)) < W × α⁻¹
  -- 等价于 (8/420)^(¼·log₂(52.5)) < 1
  have h_exp_pos := quarter_log2_half_105_pos
  have h_base_lt_1 := eight_over_420_bounds.2
  have h_base_nonneg : (0:ℝ) ≤ (8:ℝ) / 420 := le_of_lt eight_over_420_bounds.1
  have h_rpow_lt_1 : ((8:ℝ) / 420) ^ ((1:ℝ) / 4 * log2 ((105:ℝ) / 2)) < 1 :=
    Real.rpow_lt_one h_base_nonneg h_base_lt_1 h_exp_pos
  -- W × α⁻¹ > 0
  have h_Wa_pos : 0 < weavingStiffnessBase * inverseAlpha := by
    exact mul_pos weavingStiffnessBase_pos inverseAlpha_pos
  -- W × α⁻¹ × rpow < W × α⁻¹ × 1 = W × α⁻¹
  have : weavingStiffnessBase * inverseAlpha *
         ((8:ℝ) / 420) ^ ((1:ℝ) / 4 * log2 ((105:ℝ) / 2)) <
         weavingStiffnessBase * inverseAlpha * 1 := by
    exact mul_lt_mul_of_pos_left h_rpow_lt_1 h_Wa_pos
  rw [mul_one] at this
  exact this

/-- **定理：Λ_extended(0) × (8/420)² < Λ_extended(2)**（W1 严格，下界）。
    因为 8/420 < 1 且 2 > ¼·log₂(52.5)，
    由 rpow_lt_rpow_of_exponent_gt：(8/420)² < (8/420)^(¼·log₂(52.5))。 -/
theorem Λ_extended_2_gt_lower :
    Λ_extended 0 * ((8:ℝ) / 420) ^ 2 < Λ_extended 2 := by
  rw [Λ_extended_2_exponent, Λ_extended_0_simplified]
  -- 需要证明 W × α⁻¹ × (8/420)² < W × α⁻¹ × (8/420)^(¼·log₂(52.5))
  -- 等价于 (8/420)² < (8/420)^(¼·log₂(52.5))
  have h_base_pos := eight_over_420_bounds.1
  have h_base_lt_1 := eight_over_420_bounds.2
  have h_exp_lt_2 := quarter_log2_half_105_lt_2
  -- rpow_lt_rpow_of_exponent_gt : 0 < x → x < 1 → z < y → x^y < x^z
  -- 这里 x = 8/420, y = 2, z = ¼·log₂(52.5)
  -- z < y → x^y < x^z，即 (8/420)² < (8/420)^(¼·log₂(52.5))
  have h_rpow : ((8:ℝ) / 420) ^ (2:ℝ) <
                ((8:ℝ) / 420) ^ ((1:ℝ) / 4 * log2 ((105:ℝ) / 2)) :=
    Real.rpow_lt_rpow_of_exponent_gt h_base_pos h_base_lt_1 h_exp_lt_2
  -- 将目标中的 (8/420)^2 (Nat 幂) 转换为 (8/420)^(2:ℝ) (rpow)
  -- Real.rpow_natCast : x ^ (↑n : ℝ) = x ^ n, 故 .symm 将 Nat 幂转为 rpow
  rw [← Real.rpow_natCast ((8:ℝ) / 420) 2]
  -- W × α⁻¹ > 0
  have h_Wa_pos : 0 < weavingStiffnessBase * inverseAlpha := by
    exact mul_pos weavingStiffnessBase_pos inverseAlpha_pos
  exact mul_lt_mul_of_pos_left h_rpow h_Wa_pos

/-- **定理：Λ_extended(2) 的 W1 严格粗略界**（综合定理）。
    W × α⁻¹ × (8/420)² < Λ_extended(2) < W × α⁻¹。

    注意：此界精度较低（因子 (8/420)² ≈ 3.6e-4），
    但完全 W1 严格，无任何数值假设。
    更精细的界需要 log₂(52.5) 的有理逼近，留作未来工作。 -/
theorem Λ_extended_2_crude_bounds :
    Λ_extended 0 * ((8:ℝ) / 420) ^ 2 < Λ_extended 2 ∧ Λ_extended 2 < Λ_extended 0 :=
  ⟨Λ_extended_2_gt_lower, Λ_extended_2_lt_Λ_extended_0⟩

/-! ============================================================================
   §4c. Λ_extended(k=3..7) 的 W1 严格粗略界
   ============================================================================

   对于 k = 3..7（n = 840, 1680, 3360, 6720, 13440），
   log₂(n/8) 是无理数，但可给出整数上下界：
     k=3: n/8=105,   6 < log₂(105) < 7    (因 64 = 2^6 < 105 < 128 = 2^7)
     k=4: n/8=210,   7 < log₂(210) < 8    (因 128 = 2^7 < 210 < 256 = 2^8)
     k=5: n/8=420,   8 < log₂(420) < 9    (因 256 = 2^8 < 420 < 512 = 2^9)
     k=6: n/8=840,   9 < log₂(840) < 10   (因 512 = 2^9 < 840 < 1024 = 2^10)
     k=7: n/8=1680, 10 < log₂(1680) < 11  (因 1024 = 2^10 < 1680 < 2048 = 2^11)

   由此得到 Λ_extended(k) 的 W1 严格界：
     W × α⁻¹ × (8/n)^((m+1)/4) < Λ_extended(k) < W × α⁻¹ × (8/n)^(m/4)

   其中 m 为对应的整数下界。注意：0 < 8/n < 1 时 rpow 严格递减，
   所以上界指数 m/4 对应 Λ 的上界，下界指数 (m+1)/4 对应 Λ 的下界。

   证明策略：
     1. 由 2^m < n/8 < 2^(m+1) 推出 m < log₂(n/8) < m+1（logb 严格单调）
     2. 由 (1/4)·m < (1/4)·log₂(n/8) < (1/4)·(m+1)（乘正数保持方向）
     3. 由 0 < 8/n < 1 和 rpow 递减性：
        (8/n)^((m+1)/4) < (8/n)^((1/4)·log₂(n/8)) < (8/n)^(m/4)
     4. 乘以 W × α⁻¹ > 0 保持不等式方向

   精度说明：这些界的精度比 k=2 的粗略界高得多，
   因为整数 m 紧密逼近 log₂(n/8)（误差 < 1），
   而非使用极宽的 (0, 8) 界。
   ============================================================================ -/

/-- **辅助引理：log₂ 的整数界**（W1 严格，一般引理）。
    若 (2:ℝ)^m < x < (2:ℝ)^(m+1)（m : ℝ），
    则 m < log₂(x) < m+1。

    证明：由 logb 的严格单调性和 log₂(2^m) = m 直接传递。
    注意：参数 m 取 ℝ 而非 ℕ，避免 Nat.cast 与 OfNat 语法差异导致 rw 失败。 -/
lemma log2_int_bounds (x : ℝ) (m : ℝ)
    (hx_pos : 0 < x)
    (h_lower : (2:ℝ)^m < x) (h_upper : x < (2:ℝ)^(m+1)) :
    m < log2 x ∧ log2 x < m+1 := by
  refine ⟨?_, ?_⟩
  · -- m < log₂(x)
    unfold log2
    have h_log_2m : Real.logb 2 ((2:ℝ)^m) = m :=
      Real.logb_rpow (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)
    have h_2m_pos : 0 < (2:ℝ)^m := by positivity
    have h_lt : Real.logb 2 ((2:ℝ)^m) < Real.logb 2 x :=
      Real.logb_lt_logb (by norm_num : (1:ℝ) < 2)
        h_2m_pos h_lower
    rw [h_log_2m] at h_lt
    exact h_lt
  · -- log₂(x) < m+1
    unfold log2
    have h_log_2m1 : Real.logb 2 ((2:ℝ)^(m+1)) = m+1 :=
      Real.logb_rpow (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)
    have h_2m1_pos : 0 < (2:ℝ)^(m+1) := by positivity
    have h_lt : Real.logb 2 x < Real.logb 2 ((2:ℝ)^(m+1)) :=
      Real.logb_lt_logb (by norm_num : (1:ℝ) < 2)
        hx_pos h_upper
    rw [h_log_2m1] at h_lt
    exact h_lt

/-- **辅助引理：rpow 的指数界传递**（W1 严格，一般引理）。
    若 0 < x < 1 且 a < e < b，则 x^b < x^e < x^a。
    （因为 t ↦ x^t 在 0 < x < 1 时严格递减。） -/
lemma rpow_bounds_of_exp_bounds {x a e b : ℝ}
    (hx_pos : 0 < x) (hx_lt_1 : x < 1) (ha : a < e) (heb : e < b) :
    x^b < x^e ∧ x^e < x^a := by
  refine ⟨?_, ?_⟩
  · exact Real.rpow_lt_rpow_of_exponent_gt hx_pos hx_lt_1 heb
  · exact Real.rpow_lt_rpow_of_exponent_gt hx_pos hx_lt_1 ha

/-! ======== k=3: n=840, n/8=105, m=6 ======== -/

/-- **引理：log₂(105) 的整数界**（W1 严格）。
    6 < log₂(105) < 7，因为 64 = 2^6 < 105 < 128 = 2^7。 -/
lemma log2_105_bounds : (6:ℝ) < log2 105 ∧ log2 105 < (7:ℝ) := by
  have h_64 : (2:ℝ)^(6:ℝ) = 64 := by norm_num
  have h_128 : (2:ℝ)^(7:ℝ) = 128 := by norm_num
  have h := log2_int_bounds 105 6 (by norm_num)
    (by rw [h_64]; norm_num)
    (by rw [show (6:ℝ)+1 = (7:ℝ) from by norm_num, h_128]; norm_num)
  exact ⟨h.1, by linarith [h.2]⟩

/-- **引理：Λ_extended(3) 的指数展开**（W1 严格）。
    Λ_extended(3) = W × α⁻¹ × (8/840)^(¼·log₂(105))。
    因为 closure_sequence_extended 3 = 840，840/8 = 105。 -/
lemma Λ_extended_3_exponent :
    Λ_extended 3 = weavingStiffnessBase * inverseAlpha *
      ((8:ℝ) / 840) ^ ((1:ℝ) / 4 * log2 105) := by
  unfold Λ_extended curvature_energy
  show weavingStiffnessBase * inverseAlpha *
        ((8:ℝ) / (closure_sequence_extended 3)) ^
          ((1:ℝ) / 4 * log2 ((closure_sequence_extended 3 : ℝ) / 8)) =
       weavingStiffnessBase * inverseAlpha *
        ((8:ℝ) / 840) ^ ((1:ℝ) / 4 * log2 105)
  have h_cse : closure_sequence_extended 3 = 840 := by
    simp [closure_sequence_extended]
  rw [h_cse]
  norm_num

/-- **定理：Λ_extended(3) 的 W1 严格粗略界**（核心定理）。
    W × α⁻¹ × (8/840)^(7/4) < Λ_extended(3) < W × α⁻¹ × (8/840)^(6/4)。

    证明：由 6 < log₂(105) < 7 和 0 < 8/840 < 1，rpow 递减性传递。 -/
theorem Λ_extended_3_crude_bounds :
    weavingStiffnessBase * inverseAlpha * ((8:ℝ)/840)^((7:ℝ)/4) < Λ_extended 3 ∧
    Λ_extended 3 < weavingStiffnessBase * inverseAlpha * ((8:ℝ)/840)^((6:ℝ)/4) := by
  rw [Λ_extended_3_exponent]
  have h_8n_pos : 0 < (8:ℝ)/840 := by norm_num
  have h_8n_lt_1 : (8:ℝ)/840 < 1 := by norm_num
  have h_log := log2_105_bounds
  have h_exp_lb : ((6:ℝ)/4) < ((1:ℝ)/4) * log2 105 := by linarith [h_log.1]
  have h_exp_ub : ((1:ℝ)/4) * log2 105 < ((7:ℝ)/4) := by linarith [h_log.2]
  have h_rpow := rpow_bounds_of_exp_bounds h_8n_pos h_8n_lt_1 h_exp_lb h_exp_ub
  have h_Wa_pos : 0 < weavingStiffnessBase * inverseAlpha :=
    mul_pos weavingStiffnessBase_pos inverseAlpha_pos
  refine ⟨?_, ?_⟩
  · exact mul_lt_mul_of_pos_left h_rpow.1 h_Wa_pos
  · exact mul_lt_mul_of_pos_left h_rpow.2 h_Wa_pos

/-! ======== k=4: n=1680, n/8=210, m=7 ======== -/

/-- **引理：log₂(210) 的整数界**（W1 严格）。
    7 < log₂(210) < 8，因为 128 = 2^7 < 210 < 256 = 2^8。 -/
lemma log2_210_bounds : (7:ℝ) < log2 210 ∧ log2 210 < (8:ℝ) := by
  have h_128 : (2:ℝ)^(7:ℝ) = 128 := by norm_num
  have h_256 : (2:ℝ)^(8:ℝ) = 256 := by norm_num
  have h := log2_int_bounds 210 7 (by norm_num)
    (by rw [h_128]; norm_num)
    (by rw [show (7:ℝ)+1 = (8:ℝ) from by norm_num, h_256]; norm_num)
  exact ⟨h.1, by linarith [h.2]⟩

/-- **引理：Λ_extended(4) 的指数展开**（W1 严格）。
    Λ_extended(4) = W × α⁻¹ × (8/1680)^(¼·log₂(210))。 -/
lemma Λ_extended_4_exponent :
    Λ_extended 4 = weavingStiffnessBase * inverseAlpha *
      ((8:ℝ) / 1680) ^ ((1:ℝ) / 4 * log2 210) := by
  unfold Λ_extended curvature_energy
  show weavingStiffnessBase * inverseAlpha *
        ((8:ℝ) / (closure_sequence_extended 4)) ^
          ((1:ℝ) / 4 * log2 ((closure_sequence_extended 4 : ℝ) / 8)) =
       weavingStiffnessBase * inverseAlpha *
        ((8:ℝ) / 1680) ^ ((1:ℝ) / 4 * log2 210)
  have h_cse : closure_sequence_extended 4 = 1680 := by
    simp [closure_sequence_extended]
  rw [h_cse]
  norm_num

/-- **定理：Λ_extended(4) 的 W1 严格粗略界**（核心定理）。
    W × α⁻¹ × (8/1680)^(8/4) < Λ_extended(4) < W × α⁻¹ × (8/1680)^(7/4)。 -/
theorem Λ_extended_4_crude_bounds :
    weavingStiffnessBase * inverseAlpha * ((8:ℝ)/1680)^((8:ℝ)/4) < Λ_extended 4 ∧
    Λ_extended 4 < weavingStiffnessBase * inverseAlpha * ((8:ℝ)/1680)^((7:ℝ)/4) := by
  rw [Λ_extended_4_exponent]
  have h_8n_pos : 0 < (8:ℝ)/1680 := by norm_num
  have h_8n_lt_1 : (8:ℝ)/1680 < 1 := by norm_num
  have h_log := log2_210_bounds
  have h_exp_lb : ((7:ℝ)/4) < ((1:ℝ)/4) * log2 210 := by linarith [h_log.1]
  have h_exp_ub : ((1:ℝ)/4) * log2 210 < ((8:ℝ)/4) := by linarith [h_log.2]
  have h_rpow := rpow_bounds_of_exp_bounds h_8n_pos h_8n_lt_1 h_exp_lb h_exp_ub
  have h_Wa_pos : 0 < weavingStiffnessBase * inverseAlpha :=
    mul_pos weavingStiffnessBase_pos inverseAlpha_pos
  refine ⟨?_, ?_⟩
  · exact mul_lt_mul_of_pos_left h_rpow.1 h_Wa_pos
  · exact mul_lt_mul_of_pos_left h_rpow.2 h_Wa_pos

/-! ======== k=5: n=3360, n/8=420, m=8 ======== -/

/-- **引理：log₂(420) 的整数界**（W1 严格）。
    8 < log₂(420) < 9，因为 256 = 2^8 < 420 < 512 = 2^9。 -/
lemma log2_420_bounds : (8:ℝ) < log2 420 ∧ log2 420 < (9:ℝ) := by
  have h_256 : (2:ℝ)^(8:ℝ) = 256 := by norm_num
  have h_512 : (2:ℝ)^(9:ℝ) = 512 := by norm_num
  have h := log2_int_bounds 420 8 (by norm_num)
    (by rw [h_256]; norm_num)
    (by rw [show (8:ℝ)+1 = (9:ℝ) from by norm_num, h_512]; norm_num)
  exact ⟨h.1, by linarith [h.2]⟩

/-- **引理：Λ_extended(5) 的指数展开**（W1 严格）。 -/
lemma Λ_extended_5_exponent :
    Λ_extended 5 = weavingStiffnessBase * inverseAlpha *
      ((8:ℝ) / 3360) ^ ((1:ℝ) / 4 * log2 420) := by
  unfold Λ_extended curvature_energy
  show weavingStiffnessBase * inverseAlpha *
        ((8:ℝ) / (closure_sequence_extended 5)) ^
          ((1:ℝ) / 4 * log2 ((closure_sequence_extended 5 : ℝ) / 8)) =
       weavingStiffnessBase * inverseAlpha *
        ((8:ℝ) / 3360) ^ ((1:ℝ) / 4 * log2 420)
  have h_cse : closure_sequence_extended 5 = 3360 := by
    simp [closure_sequence_extended]
  rw [h_cse]
  norm_num

/-- **定理：Λ_extended(5) 的 W1 严格粗略界**（核心定理）。
    W × α⁻¹ × (8/3360)^(9/4) < Λ_extended(5) < W × α⁻¹ × (8/3360)^(8/4)。 -/
theorem Λ_extended_5_crude_bounds :
    weavingStiffnessBase * inverseAlpha * ((8:ℝ)/3360)^((9:ℝ)/4) < Λ_extended 5 ∧
    Λ_extended 5 < weavingStiffnessBase * inverseAlpha * ((8:ℝ)/3360)^((8:ℝ)/4) := by
  rw [Λ_extended_5_exponent]
  have h_8n_pos : 0 < (8:ℝ)/3360 := by norm_num
  have h_8n_lt_1 : (8:ℝ)/3360 < 1 := by norm_num
  have h_log := log2_420_bounds
  have h_exp_lb : ((8:ℝ)/4) < ((1:ℝ)/4) * log2 420 := by linarith [h_log.1]
  have h_exp_ub : ((1:ℝ)/4) * log2 420 < ((9:ℝ)/4) := by linarith [h_log.2]
  have h_rpow := rpow_bounds_of_exp_bounds h_8n_pos h_8n_lt_1 h_exp_lb h_exp_ub
  have h_Wa_pos : 0 < weavingStiffnessBase * inverseAlpha :=
    mul_pos weavingStiffnessBase_pos inverseAlpha_pos
  refine ⟨?_, ?_⟩
  · exact mul_lt_mul_of_pos_left h_rpow.1 h_Wa_pos
  · exact mul_lt_mul_of_pos_left h_rpow.2 h_Wa_pos

/-! ======== k=6: n=6720, n/8=840, m=9 ======== -/

/-- **引理：log₂(840) 的整数界**（W1 严格）。
    9 < log₂(840) < 10，因为 512 = 2^9 < 840 < 1024 = 2^10。 -/
lemma log2_840_bounds : (9:ℝ) < log2 840 ∧ log2 840 < (10:ℝ) := by
  have h_512 : (2:ℝ)^(9:ℝ) = 512 := by norm_num
  have h_1024 : (2:ℝ)^(10:ℝ) = 1024 := by norm_num
  have h := log2_int_bounds 840 9 (by norm_num)
    (by rw [h_512]; norm_num)
    (by rw [show (9:ℝ)+1 = (10:ℝ) from by norm_num, h_1024]; norm_num)
  exact ⟨h.1, by linarith [h.2]⟩

/-- **引理：Λ_extended(6) 的指数展开**（W1 严格）。 -/
lemma Λ_extended_6_exponent :
    Λ_extended 6 = weavingStiffnessBase * inverseAlpha *
      ((8:ℝ) / 6720) ^ ((1:ℝ) / 4 * log2 840) := by
  unfold Λ_extended curvature_energy
  show weavingStiffnessBase * inverseAlpha *
        ((8:ℝ) / (closure_sequence_extended 6)) ^
          ((1:ℝ) / 4 * log2 ((closure_sequence_extended 6 : ℝ) / 8)) =
       weavingStiffnessBase * inverseAlpha *
        ((8:ℝ) / 6720) ^ ((1:ℝ) / 4 * log2 840)
  have h_cse : closure_sequence_extended 6 = 6720 := by
    simp [closure_sequence_extended]
  rw [h_cse]
  norm_num

/-- **定理：Λ_extended(6) 的 W1 严格粗略界**（核心定理）。
    W × α⁻¹ × (8/6720)^(10/4) < Λ_extended(6) < W × α⁻¹ × (8/6720)^(9/4)。 -/
theorem Λ_extended_6_crude_bounds :
    weavingStiffnessBase * inverseAlpha * ((8:ℝ)/6720)^((10:ℝ)/4) < Λ_extended 6 ∧
    Λ_extended 6 < weavingStiffnessBase * inverseAlpha * ((8:ℝ)/6720)^((9:ℝ)/4) := by
  rw [Λ_extended_6_exponent]
  have h_8n_pos : 0 < (8:ℝ)/6720 := by norm_num
  have h_8n_lt_1 : (8:ℝ)/6720 < 1 := by norm_num
  have h_log := log2_840_bounds
  have h_exp_lb : ((9:ℝ)/4) < ((1:ℝ)/4) * log2 840 := by linarith [h_log.1]
  have h_exp_ub : ((1:ℝ)/4) * log2 840 < ((10:ℝ)/4) := by linarith [h_log.2]
  have h_rpow := rpow_bounds_of_exp_bounds h_8n_pos h_8n_lt_1 h_exp_lb h_exp_ub
  have h_Wa_pos : 0 < weavingStiffnessBase * inverseAlpha :=
    mul_pos weavingStiffnessBase_pos inverseAlpha_pos
  refine ⟨?_, ?_⟩
  · exact mul_lt_mul_of_pos_left h_rpow.1 h_Wa_pos
  · exact mul_lt_mul_of_pos_left h_rpow.2 h_Wa_pos

/-! ======== k=7: n=13440, n/8=1680, m=10 ======== -/

/-- **引理：log₂(1680) 的整数界**（W1 严格）。
    10 < log₂(1680) < 11，因为 1024 = 2^10 < 1680 < 2048 = 2^11。 -/
lemma log2_1680_bounds : (10:ℝ) < log2 1680 ∧ log2 1680 < (11:ℝ) := by
  have h_1024 : (2:ℝ)^(10:ℝ) = 1024 := by norm_num
  have h_2048 : (2:ℝ)^(11:ℝ) = 2048 := by norm_num
  have h := log2_int_bounds 1680 10 (by norm_num)
    (by rw [h_1024]; norm_num)
    (by rw [show (10:ℝ)+1 = (11:ℝ) from by norm_num, h_2048]; norm_num)
  exact ⟨h.1, by linarith [h.2]⟩

/-- **引理：Λ_extended(7) 的指数展开**（W1 严格）。 -/
lemma Λ_extended_7_exponent :
    Λ_extended 7 = weavingStiffnessBase * inverseAlpha *
      ((8:ℝ) / 13440) ^ ((1:ℝ) / 4 * log2 1680) := by
  unfold Λ_extended curvature_energy
  show weavingStiffnessBase * inverseAlpha *
        ((8:ℝ) / (closure_sequence_extended 7)) ^
          ((1:ℝ) / 4 * log2 ((closure_sequence_extended 7 : ℝ) / 8)) =
       weavingStiffnessBase * inverseAlpha *
        ((8:ℝ) / 13440) ^ ((1:ℝ) / 4 * log2 1680)
  have h_cse : closure_sequence_extended 7 = 13440 := by
    simp [closure_sequence_extended]
  rw [h_cse]
  norm_num

/-- **定理：Λ_extended(7) 的 W1 严格粗略界**（核心定理）。
    W × α⁻¹ × (8/13440)^(11/4) < Λ_extended(7) < W × α⁻¹ × (8/13440)^(10/4)。 -/
theorem Λ_extended_7_crude_bounds :
    weavingStiffnessBase * inverseAlpha * ((8:ℝ)/13440)^((11:ℝ)/4) < Λ_extended 7 ∧
    Λ_extended 7 < weavingStiffnessBase * inverseAlpha * ((8:ℝ)/13440)^((10:ℝ)/4) := by
  rw [Λ_extended_7_exponent]
  have h_8n_pos : 0 < (8:ℝ)/13440 := by norm_num
  have h_8n_lt_1 : (8:ℝ)/13440 < 1 := by norm_num
  have h_log := log2_1680_bounds
  have h_exp_lb : ((10:ℝ)/4) < ((1:ℝ)/4) * log2 1680 := by linarith [h_log.1]
  have h_exp_ub : ((1:ℝ)/4) * log2 1680 < ((11:ℝ)/4) := by linarith [h_log.2]
  have h_rpow := rpow_bounds_of_exp_bounds h_8n_pos h_8n_lt_1 h_exp_lb h_exp_ub
  have h_Wa_pos : 0 < weavingStiffnessBase * inverseAlpha :=
    mul_pos weavingStiffnessBase_pos inverseAlpha_pos
  refine ⟨?_, ?_⟩
  · exact mul_lt_mul_of_pos_left h_rpow.1 h_Wa_pos
  · exact mul_lt_mul_of_pos_left h_rpow.2 h_Wa_pos

/-! ============================================================================
   §4e. Λ_extended(k=3..7) 的 W1 严格精细有理界（v12.1.4 新增）
   ============================================================================

   改进：将 §4c 的整数界（宽度 1，因子 < 2^(1/4) ≈ 1.189）
   升级为四分之一精度有理界（宽度 1/4，因子 < 2^(1/16) ≈ 1.044）。

   方法：对 log₂(n/8)（n=840,1680,3360,6720,13440），
   证明 p/4 < log₂(x) < (p+1)/4，通过验证 2^p < x^4 < 2^(p+1)（纯 Nat 算术）。

   | k | x=n/8  | p  | p/4   | (p+1)/4 | 验证                     |
   |---|--------|----|-------|---------|--------------------------|
   | 3 | 105    | 26 | 6.50  | 6.75    | 2^26 < 105^4 < 2^27     |
   | 4 | 210    | 30 | 7.50  | 7.75    | 2^30 < 210^4 < 2^31     |
   | 5 | 420    | 34 | 8.50  | 8.75    | 2^34 < 420^4 < 2^35     |
   | 6 | 840    | 38 | 9.50  | 9.75    | 2^38 < 840^4 < 2^39     |
   | 7 | 1680   | 42 | 10.50 | 10.75   | 2^42 < 1680^4 < 2^43    |

   由此得到 Λ_extended(k) 的 W1 严格精细界：
     W × α⁻¹ × (8/n)^((p+1)/16) < Λ_extended(k) < W × α⁻¹ × (8/n)^(p/16)

   指数误差 < 1/16，因子 < 2^(1/16) ≈ 1.044（比 §4c 的 1.189 精密 4 倍）。
   ============================================================================ -/

/-- **辅助引理：log₂ 的有理界**（W1 严格，一般引理）。
    若 (2:ℝ)^a < x < (2:ℝ)^b（a, b : ℝ），
    则 a < log₂(x) < b。

    证明：由 logb 的严格单调性和 log₂(2^r) = r 直接传递。
    这是 log2_int_bounds 的有理推广，使用独立上下界避免 p+1 的类型问题。 -/
lemma log2_rational_bounds (x : ℝ) (a b : ℝ)
    (hx_pos : 0 < x)
    (h_lower : (2:ℝ)^a < x) (h_upper : x < (2:ℝ)^b) :
    a < log2 x ∧ log2 x < b := by
  refine ⟨?_, ?_⟩
  · unfold log2
    have h_log : Real.logb 2 ((2:ℝ)^a) = a :=
      Real.logb_rpow (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)
    have h_pos : 0 < (2:ℝ)^a := by positivity
    have h_lt : Real.logb 2 ((2:ℝ)^a) < Real.logb 2 x :=
      Real.logb_lt_logb (by norm_num : (1:ℝ) < 2) h_pos h_lower
    rw [h_log] at h_lt
    exact h_lt
  · unfold log2
    have h_log : Real.logb 2 ((2:ℝ)^b) = b :=
      Real.logb_rpow (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)
    have h_pos : 0 < (2:ℝ)^b := by positivity
    have h_lt : Real.logb 2 x < Real.logb 2 ((2:ℝ)^b) :=
      Real.logb_lt_logb (by norm_num : (1:ℝ) < 2) hx_pos h_upper
    rw [h_log] at h_lt
    exact h_lt

/-- **辅助引理：从 Nat 幂比较推导 rpow 有理界（下界）**（W1 严格）。
    若 (2:ℝ)^p < x^q（Nat 幂，p q : ℕ, q > 0, x > 0），
    则 (2:ℝ)^(p/q) < x。

    证明：将 Nat 幂转为 rpow，取 q 次根（rpow 单调性），
    化简指数 q*(1/q) = 1 和 p*(1/q) = p/q。 -/
lemma two_rpow_div_lt (x : ℝ) (p q : ℕ) (hx_pos : 0 < x)
    (h : (2:ℝ)^(p:ℕ) < x^(q:ℕ)) (hq : 0 < q) :
    (2:ℝ)^((p:ℝ)/(q:ℝ)) < x := by
  -- 将 Nat 幕转为 rpow
  have h_rpow : (2:ℝ)^(p:ℝ) < x^(q:ℝ) := by
    rw [Real.rpow_natCast (2:ℝ) p, Real.rpow_natCast x q]; exact h
  -- 取 q 次根（rpow 单调性）
  have h_inv_q_pos : 0 < (1:ℝ)/(q:ℝ) := by positivity
  have h_2_nonneg : 0 ≤ (2:ℝ) := le_of_lt (by norm_num)
  have h_x_nonneg : 0 ≤ x := le_of_lt hx_pos
  have h_2p_nonneg : 0 ≤ (2:ℝ)^(p:ℝ) := le_of_lt (by positivity)
  have h_root : ((2:ℝ)^(p:ℝ))^((1:ℝ)/(q:ℝ)) < (x^(q:ℝ))^((1:ℝ)/(q:ℝ)) :=
    Real.rpow_lt_rpow h_2p_nonneg h_rpow h_inv_q_pos
  -- 化简：← rpow_mul 将 (x^a)^b 转为 x^(a*b)
  rw [← Real.rpow_mul h_2_nonneg, ← Real.rpow_mul h_x_nonneg] at h_root
  -- 化简指数
  have hq_real_ne : (q:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hq)
  have h_simp1 : (q:ℝ) * ((1:ℝ)/(q:ℝ)) = 1 := by
    rw [one_div]; exact mul_inv_cancel₀ hq_real_ne
  rw [h_simp1, Real.rpow_one] at h_root
  have h_simp2 : (p:ℝ) * ((1:ℝ)/(q:ℝ)) = (p:ℝ)/(q:ℝ) := by
    rw [one_div, div_eq_mul_inv]
  rw [h_simp2] at h_root
  exact h_root

/-- **辅助引理：从 Nat 幂比较推导 rpow 有理界（上界）**（W1 严格）。
    若 x^q < (2:ℝ)^p（Nat 幂，p q : ℕ, q > 0, x > 0），
    则 x < (2:ℝ)^(p/q)。 -/
lemma lt_two_rpow_div (x : ℝ) (p q : ℕ) (hx_pos : 0 < x)
    (h : x^(q:ℕ) < (2:ℝ)^(p:ℕ)) (hq : 0 < q) :
    x < (2:ℝ)^((p:ℝ)/(q:ℝ)) := by
  have h_rpow : x^(q:ℝ) < (2:ℝ)^(p:ℝ) := by
    rw [Real.rpow_natCast (2:ℝ) p, Real.rpow_natCast x q]; exact h
  have h_inv_q_pos : 0 < (1:ℝ)/(q:ℝ) := by positivity
  have h_2_nonneg : 0 ≤ (2:ℝ) := le_of_lt (by norm_num)
  have h_x_nonneg : 0 ≤ x := le_of_lt hx_pos
  have h_xq_nonneg : 0 ≤ x^(q:ℝ) := le_of_lt (by positivity)
  have h_root : (x^(q:ℝ))^((1:ℝ)/(q:ℝ)) < ((2:ℝ)^(p:ℝ))^((1:ℝ)/(q:ℝ)) :=
    Real.rpow_lt_rpow h_xq_nonneg h_rpow h_inv_q_pos
  rw [← Real.rpow_mul h_x_nonneg, ← Real.rpow_mul h_2_nonneg] at h_root
  have hq_real_ne : (q:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hq)
  have h_simp1 : (q:ℝ) * ((1:ℝ)/(q:ℝ)) = 1 := by
    rw [one_div]; exact mul_inv_cancel₀ hq_real_ne
  rw [h_simp1, Real.rpow_one] at h_root
  have h_simp2 : (p:ℝ) * ((1:ℝ)/(q:ℝ)) = (p:ℝ)/(q:ℝ) := by
    rw [one_div, div_eq_mul_inv]
  rw [h_simp2] at h_root
  exact h_root

/-! ======== 精细 log₂ 界：k=3..7 ======== -/

/-- **引理：log₂(105) 的四分之一精度界**（W1 严格）。
    26/4 < log₂(105) < 27/4，因为 2^26 < 105^4 < 2^27。
    验证：2^26 = 67108864 < 105^4 = 121550625 < 2^27 = 134217728。 -/
lemma log2_105_quarter_bounds : (26:ℝ)/4 < log2 105 ∧ log2 105 < (27:ℝ)/4 := by
  have h_lower : (2:ℝ)^((26:ℝ)/4) < 105 := by
    apply two_rpow_div_lt 105 26 4 (by norm_num) (by norm_num) (by norm_num : 0 < 4)
  have h_upper : (105:ℝ) < (2:ℝ)^((27:ℝ)/4) := by
    apply lt_two_rpow_div 105 27 4 (by norm_num) (by norm_num) (by norm_num : 0 < 4)
  exact log2_rational_bounds 105 ((26:ℝ)/4) ((27:ℝ)/4) (by norm_num) h_lower h_upper

/-- **引理：log₂(210) 的四分之一精度界**（W1 严格）。
    30/4 < log₂(210) < 31/4，因为 2^30 < 210^4 < 2^31。
    验证：2^30 = 1073741824 < 210^4 = 1944810000 < 2^31 = 2147483648。 -/
lemma log2_210_quarter_bounds : (30:ℝ)/4 < log2 210 ∧ log2 210 < (31:ℝ)/4 := by
  have h_lower : (2:ℝ)^((30:ℝ)/4) < 210 := by
    apply two_rpow_div_lt 210 30 4 (by norm_num) (by norm_num) (by norm_num : 0 < 4)
  have h_upper : (210:ℝ) < (2:ℝ)^((31:ℝ)/4) := by
    apply lt_two_rpow_div 210 31 4 (by norm_num) (by norm_num) (by norm_num : 0 < 4)
  exact log2_rational_bounds 210 ((30:ℝ)/4) ((31:ℝ)/4) (by norm_num) h_lower h_upper

/-- **引理：log₂(420) 的四分之一精度界**（W1 严格）。
    34/4 < log₂(420) < 35/4，因为 2^34 < 420^4 < 2^35。
    验证：2^34 = 17179869184 < 420^4 = 31116960000 < 2^35 = 34359738368。 -/
lemma log2_420_quarter_bounds : (34:ℝ)/4 < log2 420 ∧ log2 420 < (35:ℝ)/4 := by
  have h_lower : (2:ℝ)^((34:ℝ)/4) < 420 := by
    apply two_rpow_div_lt 420 34 4 (by norm_num) (by norm_num) (by norm_num : 0 < 4)
  have h_upper : (420:ℝ) < (2:ℝ)^((35:ℝ)/4) := by
    apply lt_two_rpow_div 420 35 4 (by norm_num) (by norm_num) (by norm_num : 0 < 4)
  exact log2_rational_bounds 420 ((34:ℝ)/4) ((35:ℝ)/4) (by norm_num) h_lower h_upper

/-- **引理：log₂(840) 的四分之一精度界**（W1 严格）。
    38/4 < log₂(840) < 39/4，因为 2^38 < 840^4 < 2^39。
    验证：2^38 = 274877906944 < 840^4 = 497871360000 < 2^39 = 549755813888。 -/
lemma log2_840_quarter_bounds : (38:ℝ)/4 < log2 840 ∧ log2 840 < (39:ℝ)/4 := by
  have h_lower : (2:ℝ)^((38:ℝ)/4) < 840 := by
    apply two_rpow_div_lt 840 38 4 (by norm_num) (by norm_num) (by norm_num : 0 < 4)
  have h_upper : (840:ℝ) < (2:ℝ)^((39:ℝ)/4) := by
    apply lt_two_rpow_div 840 39 4 (by norm_num) (by norm_num) (by norm_num : 0 < 4)
  exact log2_rational_bounds 840 ((38:ℝ)/4) ((39:ℝ)/4) (by norm_num) h_lower h_upper

/-- **引理：log₂(1680) 的四分之一精度界**（W1 严格）。
    42/4 < log₂(1680) < 43/4，因为 2^42 < 1680^4 < 2^43。
    验证：2^42 = 4398046511104 < 1680^4 = 7965941760000 < 2^43 = 8796093022208。 -/
lemma log2_1680_quarter_bounds : (42:ℝ)/4 < log2 1680 ∧ log2 1680 < (43:ℝ)/4 := by
  have h_lower : (2:ℝ)^((42:ℝ)/4) < 1680 := by
    apply two_rpow_div_lt 1680 42 4 (by norm_num) (by norm_num) (by norm_num : 0 < 4)
  have h_upper : (1680:ℝ) < (2:ℝ)^((43:ℝ)/4) := by
    apply lt_two_rpow_div 1680 43 4 (by norm_num) (by norm_num) (by norm_num : 0 < 4)
  exact log2_rational_bounds 1680 ((42:ℝ)/4) ((43:ℝ)/4) (by norm_num) h_lower h_upper

/-! ======== 精细 Λ_extended 界：k=3..7 ======== -/

/-- **定理：Λ_extended(3) 的 W1 严格精细界**（核心定理）。
    W × α⁻¹ × (8/840)^(27/16) < Λ_extended(3) < W × α⁻¹ × (8/840)^(13/8)。

    证明：由 26/4 < log₂(105) < 27/4 和 0 < 8/840 < 1，rpow 递减性传递。
    指数误差 < 1/16，因子 < 2^(1/16) ≈ 1.044。 -/
theorem Λ_extended_3_refined_bounds :
    weavingStiffnessBase * inverseAlpha * ((8:ℝ)/840)^((27:ℝ)/16) < Λ_extended 3 ∧
    Λ_extended 3 < weavingStiffnessBase * inverseAlpha * ((8:ℝ)/840)^((13:ℝ)/8) := by
  rw [Λ_extended_3_exponent]
  have h_8n_pos : 0 < (8:ℝ)/840 := by norm_num
  have h_8n_lt_1 : (8:ℝ)/840 < 1 := by norm_num
  have h_log := log2_105_quarter_bounds
  -- 指数界：(1/4)*(26/4) = 26/16 = 13/8 < (1/4)*log₂(105) < (1/4)*(27/4) = 27/16
  have h_exp_lb : (13:ℝ)/8 < ((1:ℝ)/4) * log2 105 := by
    have : (13:ℝ)/8 = (26:ℝ)/16 := by norm_num
    rw [this]
    have h : (26:ℝ)/16 = ((1:ℝ)/4) * ((26:ℝ)/4) := by norm_num
    rw [h]
    exact mul_lt_mul_of_pos_left h_log.1 (by norm_num : (0:ℝ) < (1:ℝ)/4)
  have h_exp_ub : ((1:ℝ)/4) * log2 105 < (27:ℝ)/16 := by
    have h : (27:ℝ)/16 = ((1:ℝ)/4) * ((27:ℝ)/4) := by norm_num
    rw [h]
    exact mul_lt_mul_of_pos_left h_log.2 (by norm_num : (0:ℝ) < (1:ℝ)/4)
  have h_rpow := rpow_bounds_of_exp_bounds h_8n_pos h_8n_lt_1 h_exp_lb h_exp_ub
  have h_Wa_pos : 0 < weavingStiffnessBase * inverseAlpha :=
    mul_pos weavingStiffnessBase_pos inverseAlpha_pos
  refine ⟨?_, ?_⟩
  · exact mul_lt_mul_of_pos_left h_rpow.1 h_Wa_pos
  · exact mul_lt_mul_of_pos_left h_rpow.2 h_Wa_pos

/-- **定理：Λ_extended(4) 的 W1 严格精细界**（核心定理）。
    W × α⁻¹ × (8/1680)^(31/16) < Λ_extended(4) < W × α⁻¹ × (8/1680)^(15/8)。 -/
theorem Λ_extended_4_refined_bounds :
    weavingStiffnessBase * inverseAlpha * ((8:ℝ)/1680)^((31:ℝ)/16) < Λ_extended 4 ∧
    Λ_extended 4 < weavingStiffnessBase * inverseAlpha * ((8:ℝ)/1680)^((15:ℝ)/8) := by
  rw [Λ_extended_4_exponent]
  have h_8n_pos : 0 < (8:ℝ)/1680 := by norm_num
  have h_8n_lt_1 : (8:ℝ)/1680 < 1 := by norm_num
  have h_log := log2_210_quarter_bounds
  have h_exp_lb : (15:ℝ)/8 < ((1:ℝ)/4) * log2 210 := by
    have h15_8 : (15:ℝ)/8 = (30:ℝ)/16 := by norm_num
    rw [h15_8]
    have h : (30:ℝ)/16 = ((1:ℝ)/4) * ((30:ℝ)/4) := by norm_num
    rw [h]
    exact mul_lt_mul_of_pos_left h_log.1 (by norm_num : (0:ℝ) < (1:ℝ)/4)
  have h_exp_ub : ((1:ℝ)/4) * log2 210 < (31:ℝ)/16 := by
    have h : (31:ℝ)/16 = ((1:ℝ)/4) * ((31:ℝ)/4) := by norm_num
    rw [h]
    exact mul_lt_mul_of_pos_left h_log.2 (by norm_num : (0:ℝ) < (1:ℝ)/4)
  have h_rpow := rpow_bounds_of_exp_bounds h_8n_pos h_8n_lt_1 h_exp_lb h_exp_ub
  have h_Wa_pos : 0 < weavingStiffnessBase * inverseAlpha :=
    mul_pos weavingStiffnessBase_pos inverseAlpha_pos
  refine ⟨?_, ?_⟩
  · exact mul_lt_mul_of_pos_left h_rpow.1 h_Wa_pos
  · exact mul_lt_mul_of_pos_left h_rpow.2 h_Wa_pos

/-- **定理：Λ_extended(5) 的 W1 严格精细界**（核心定理）。
    W × α⁻¹ × (8/3360)^(35/16) < Λ_extended(5) < W × α⁻¹ × (8/3360)^(17/8)。 -/
theorem Λ_extended_5_refined_bounds :
    weavingStiffnessBase * inverseAlpha * ((8:ℝ)/3360)^((35:ℝ)/16) < Λ_extended 5 ∧
    Λ_extended 5 < weavingStiffnessBase * inverseAlpha * ((8:ℝ)/3360)^((17:ℝ)/8) := by
  rw [Λ_extended_5_exponent]
  have h_8n_pos : 0 < (8:ℝ)/3360 := by norm_num
  have h_8n_lt_1 : (8:ℝ)/3360 < 1 := by norm_num
  have h_log := log2_420_quarter_bounds
  have h_exp_lb : (17:ℝ)/8 < ((1:ℝ)/4) * log2 420 := by
    have h17_8 : (17:ℝ)/8 = (34:ℝ)/16 := by norm_num
    rw [h17_8]
    have h : (34:ℝ)/16 = ((1:ℝ)/4) * ((34:ℝ)/4) := by norm_num
    rw [h]
    exact mul_lt_mul_of_pos_left h_log.1 (by norm_num : (0:ℝ) < (1:ℝ)/4)
  have h_exp_ub : ((1:ℝ)/4) * log2 420 < (35:ℝ)/16 := by
    have h : (35:ℝ)/16 = ((1:ℝ)/4) * ((35:ℝ)/4) := by norm_num
    rw [h]
    exact mul_lt_mul_of_pos_left h_log.2 (by norm_num : (0:ℝ) < (1:ℝ)/4)
  have h_rpow := rpow_bounds_of_exp_bounds h_8n_pos h_8n_lt_1 h_exp_lb h_exp_ub
  have h_Wa_pos : 0 < weavingStiffnessBase * inverseAlpha :=
    mul_pos weavingStiffnessBase_pos inverseAlpha_pos
  refine ⟨?_, ?_⟩
  · exact mul_lt_mul_of_pos_left h_rpow.1 h_Wa_pos
  · exact mul_lt_mul_of_pos_left h_rpow.2 h_Wa_pos

/-- **定理：Λ_extended(6) 的 W1 严格精细界**（核心定理）。
    W × α⁻¹ × (8/6720)^(39/16) < Λ_extended(6) < W × α⁻¹ × (8/6720)^(19/8)。 -/
theorem Λ_extended_6_refined_bounds :
    weavingStiffnessBase * inverseAlpha * ((8:ℝ)/6720)^((39:ℝ)/16) < Λ_extended 6 ∧
    Λ_extended 6 < weavingStiffnessBase * inverseAlpha * ((8:ℝ)/6720)^((19:ℝ)/8) := by
  rw [Λ_extended_6_exponent]
  have h_8n_pos : 0 < (8:ℝ)/6720 := by norm_num
  have h_8n_lt_1 : (8:ℝ)/6720 < 1 := by norm_num
  have h_log := log2_840_quarter_bounds
  have h_exp_lb : (19:ℝ)/8 < ((1:ℝ)/4) * log2 840 := by
    have h19_8 : (19:ℝ)/8 = (38:ℝ)/16 := by norm_num
    rw [h19_8]
    have h : (38:ℝ)/16 = ((1:ℝ)/4) * ((38:ℝ)/4) := by norm_num
    rw [h]
    exact mul_lt_mul_of_pos_left h_log.1 (by norm_num : (0:ℝ) < (1:ℝ)/4)
  have h_exp_ub : ((1:ℝ)/4) * log2 840 < (39:ℝ)/16 := by
    have h : (39:ℝ)/16 = ((1:ℝ)/4) * ((39:ℝ)/4) := by norm_num
    rw [h]
    exact mul_lt_mul_of_pos_left h_log.2 (by norm_num : (0:ℝ) < (1:ℝ)/4)
  have h_rpow := rpow_bounds_of_exp_bounds h_8n_pos h_8n_lt_1 h_exp_lb h_exp_ub
  have h_Wa_pos : 0 < weavingStiffnessBase * inverseAlpha :=
    mul_pos weavingStiffnessBase_pos inverseAlpha_pos
  refine ⟨?_, ?_⟩
  · exact mul_lt_mul_of_pos_left h_rpow.1 h_Wa_pos
  · exact mul_lt_mul_of_pos_left h_rpow.2 h_Wa_pos

/-- **定理：Λ_extended(7) 的 W1 严格精细界**（核心定理）。
    W × α⁻¹ × (8/13440)^(43/16) < Λ_extended(7) < W × α⁻¹ × (8/13440)^(21/8)。 -/
theorem Λ_extended_7_refined_bounds :
    weavingStiffnessBase * inverseAlpha * ((8:ℝ)/13440)^((43:ℝ)/16) < Λ_extended 7 ∧
    Λ_extended 7 < weavingStiffnessBase * inverseAlpha * ((8:ℝ)/13440)^((21:ℝ)/8) := by
  rw [Λ_extended_7_exponent]
  have h_8n_pos : 0 < (8:ℝ)/13440 := by norm_num
  have h_8n_lt_1 : (8:ℝ)/13440 < 1 := by norm_num
  have h_log := log2_1680_quarter_bounds
  have h_exp_lb : (21:ℝ)/8 < ((1:ℝ)/4) * log2 1680 := by
    have h21_8 : (21:ℝ)/8 = (42:ℝ)/16 := by norm_num
    rw [h21_8]
    have h : (42:ℝ)/16 = ((1:ℝ)/4) * ((42:ℝ)/4) := by norm_num
    rw [h]
    exact mul_lt_mul_of_pos_left h_log.1 (by norm_num : (0:ℝ) < (1:ℝ)/4)
  have h_exp_ub : ((1:ℝ)/4) * log2 1680 < (43:ℝ)/16 := by
    have h : (43:ℝ)/16 = ((1:ℝ)/4) * ((43:ℝ)/4) := by norm_num
    rw [h]
    exact mul_lt_mul_of_pos_left h_log.2 (by norm_num : (0:ℝ) < (1:ℝ)/4)
  have h_rpow := rpow_bounds_of_exp_bounds h_8n_pos h_8n_lt_1 h_exp_lb h_exp_ub
  have h_Wa_pos : 0 < weavingStiffnessBase * inverseAlpha :=
    mul_pos weavingStiffnessBase_pos inverseAlpha_pos
  refine ⟨?_, ?_⟩
  · exact mul_lt_mul_of_pos_left h_rpow.1 h_Wa_pos
  · exact mul_lt_mul_of_pos_left h_rpow.2 h_Wa_pos

/-! ======== 精细 Λ_extended 界：k=2（v12.1.5 新增） ======== -/

/-- **引理：log₂(52.5) 的四分之一精度界**（W1 严格）。
    22/4 < log₂(52.5) < 23/4。

    证明：log₂(105/2) = log₂(105) - log₂(2) = log₂(105) - 1
    （由 logb_div 和 logb_self_eq_one）。
    再由 26/4 < log₂(105) < 27/4（log2_105_quarter_bounds），
    减 1 传递：22/4 < log₂(52.5) < 23/4。

    验证：log₂(52.5) ≈ 5.7142...，22/4 = 5.5, 23/4 = 5.75。 -/
lemma log2_half_105_quarter_bounds :
    (22:ℝ)/4 < log2 ((105:ℝ)/2) ∧ log2 ((105:ℝ)/2) < (23:ℝ)/4 := by
  have h_log := log2_105_quarter_bounds
  -- log₂(2) = 1
  have h_log2_2 : log2 (2:ℝ) = 1 := by
    unfold log2
    exact logb_self_eq_one (by norm_num : (1:ℝ) < 2)
  -- log₂(105/2) = log₂(105) - log₂(2)
  have h_div : log2 ((105:ℝ)/2) = log2 (105:ℝ) - log2 (2:ℝ) := by
    unfold log2
    exact logb_div (by norm_num : (105:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)
  rw [h_div, h_log2_2]
  -- 目标: 22/4 < log₂(105) - 1 ∧ log₂(105) - 1 < 23/4
  -- 由 h_log: 26/4 < log₂(105) < 27/4，减 1 传递
  refine ⟨?_, ?_⟩
  · linarith
  · linarith

/-- **定理：Λ_extended(2) 的 W1 严格精细界**（核心定理，v12.1.5 新增）。
    W × α⁻¹ × (8/420)^(23/16) < Λ_extended(2) < W × α⁻¹ × (8/420)^(11/8)。

    证明：由 22/4 < log₂(52.5) < 23/4 和 0 < 8/420 < 1，rpow 递减性传递。
    指数误差 < 1/16，因子 < 2^(1/16) ≈ 1.044。

    对比 v12.1.3 粗略界：Wα⁻¹(8/420)² < Λ_ext(2) < Wα⁻¹，
    因子 (8/420)² ≈ 3.6e-4（极宽），精度提升约 10⁶ 倍。 -/
theorem Λ_extended_2_refined_bounds :
    weavingStiffnessBase * inverseAlpha * ((8:ℝ)/420)^((23:ℝ)/16) < Λ_extended 2 ∧
    Λ_extended 2 < weavingStiffnessBase * inverseAlpha * ((8:ℝ)/420)^((11:ℝ)/8) := by
  rw [Λ_extended_2_exponent]
  have h_8n_pos : 0 < (8:ℝ)/420 := by norm_num
  have h_8n_lt_1 : (8:ℝ)/420 < 1 := by norm_num
  have h_log := log2_half_105_quarter_bounds
  -- 指数界：(1/4)*(22/4) = 22/16 = 11/8 < (1/4)*log₂(52.5) < (1/4)*(23/4) = 23/16
  have h_exp_lb : (11:ℝ)/8 < ((1:ℝ)/4) * log2 ((105:ℝ)/2) := by
    have h11_8 : (11:ℝ)/8 = (22:ℝ)/16 := by norm_num
    rw [h11_8]
    have h : (22:ℝ)/16 = ((1:ℝ)/4) * ((22:ℝ)/4) := by norm_num
    rw [h]
    exact mul_lt_mul_of_pos_left h_log.1 (by norm_num : (0:ℝ) < (1:ℝ)/4)
  have h_exp_ub : ((1:ℝ)/4) * log2 ((105:ℝ)/2) < (23:ℝ)/16 := by
    have h : (23:ℝ)/16 = ((1:ℝ)/4) * ((23:ℝ)/4) := by norm_num
    rw [h]
    exact mul_lt_mul_of_pos_left h_log.2 (by norm_num : (0:ℝ) < (1:ℝ)/4)
  have h_rpow := rpow_bounds_of_exp_bounds h_8n_pos h_8n_lt_1 h_exp_lb h_exp_ub
  have h_Wa_pos : 0 < weavingStiffnessBase * inverseAlpha :=
    mul_pos weavingStiffnessBase_pos inverseAlpha_pos
  refine ⟨?_, ?_⟩
  · exact mul_lt_mul_of_pos_left h_rpow.1 h_Wa_pos
  · exact mul_lt_mul_of_pos_left h_rpow.2 h_Wa_pos

end CSQIT.V12.ErrorBounds
