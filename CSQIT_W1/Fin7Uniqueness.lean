/-
================================================================================
CSQIT W1 — Fin 7 唯一性定理（移植自 v12）
文件: CSQIT_W1/Fin7Uniqueness.lean
版本: v15.0.0（物理扩展版）
日期: 2026-10-02

================================================================================
理论层级标注
================================================================================
  §0：分圆域基本恒等式 —— 🟡 Axiom（高斯 1801 年标准结果，数学已证 200 年）
  §1-§4：代数扩张次数、可逆/不可逆性门槛 —— 🔵 W1 严格（纯数学）
  §5-§6：结构形成窗口、素数排除 —— 🔵 W1 严格（cos 单调性 + 有理界）
    其中 IsStructureForming 的窗口 (0.28, 0.33) 本身是 🟢 W2 经验约束
  §B：桥接到 Foundation.k_out_Fin7 —— 🔵 W1 严格（定义直接关联）
  §7：Fin 7 唯一性综合定理 —— 🟢 W2 条件性（W1 定理 + W2 窗口约束）

================================================================================
与 Foundation 的桥接关系（§B 新增）
================================================================================

  Foundation §4.2 定义：k_out_Fin7 = 1 + 2cos(2π/7)
  本文件定义：theta_p p = 1 / (2 + 2cos(2π/p))

  直接关联定理：
    theta_p 7 = 1 / (1 + k_out_Fin7)

  物理意义链：
    基底 MUST_HAVE ∋ 7（W1）
      ↓
    k_out_Fin7 = 1 + 2cos(2π/7)（W1，Foundation §4.2）
      ↓
    gravitationalQuantumFromFin7 = 1/k_out²（W1，Foundation §4.2）
    theta_p 7 = 1/(1+k_out) ∈ (0.28, 0.33)（W1 严格界，本文件 §5.5）
      ↓
    fin7_uniqueness：p=7 是唯一满足不可逆性 + 结构形成的素数（W2 综合）

================================================================================
移植说明
================================================================================

  从 V12/Core/Fin7Uniqueness.lean 移植，做以下修改：
  1. namespace CSQIT.V12.Fin7Uniqueness → CSQIT_W1.Fin7Uniqueness
  2. 新增 §B 桥接定理，关联 Foundation.k_out_Fin7
  3. 新增 §B 的物理意义注释
  4. import 加入 CSQIT_W1.Foundation
================================================================================
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp
import CSQIT_W1.Foundation

namespace CSQIT_W1.Fin7Uniqueness

open Real

/-! ============================================================================
   §0. 分圆域 ℚ(ζ₇) 的基本恒等式（高斯 1801）
   
   以下两个数学事实来自分圆域理论。
   我们以 axiom 形式引入，因为完整证明需要复数分析和分圆多项式理论，
   但这些结果在人类数学中已被严格证明超过 200 年。
   
   手写证明（数学可验证）：
   
   引理 A：α₁ + α₂ + α₃ = -1
     由 1 + ζ + ζ² + ζ³ + ζ⁴ + ζ⁵ + ζ⁶ = 0（几何级数）
     配对共轭项：1 + (ζ+ζ⁶) + (ζ²+ζ⁵) + (ζ³+ζ⁴) = 0
     即 1 + 2cos(2π/7) + 2cos(4π/7) + 2cos(6π/7) = 0 ✓
   
   引理 B：α₁ 满足 x³ + x² - 2x - 1 = 0
     从 Φ₇(ζ⁶+ζ⁵+ζ⁴+ζ³+ζ²+ζ+1=0) 除以 ζ³
     令 y = ζ + ζ⁻¹ = α₁，则 y³ + y² - 2y - 1 = 0 ✓
   ============================================================================ -/

/-- **7 次单位根的实部**：2cos(2πk/7) -/
noncomputable def seventh_root_real_part (k : ℕ) : ℝ :=
  2 * Real.cos (2 * (k : ℝ) * Real.pi / 7)

/-- **引理 A（分圆域定理）**：α₁ + α₂ + α₃ = -1。 -/
axiom seventh_root_sum_neg_one :
    seventh_root_real_part 1 + seventh_root_real_part 2 + seventh_root_real_part 3 = -1

/-- **引理 B（分圆域定理）**：α₁ 满足 x³ + x² - 2x - 1 = 0。 -/
axiom cos2pi7_cubic_equation :
    let α := seventh_root_real_part 1
    α^3 + α^2 - 2 * α - 1 = 0

/-! ============================================================================
   §1. 代数扩张次数的形式化定义
   
   核心概念：素数 p 对应的循环群 Fin p 的"代数复杂度"由
   分圆域 Q(ζ_p) 的实子域的扩张次数 d = (p-1)/2 决定。
   
   d=1 (p=3): 实子域 = Q 本身，结构平凡 → 可逆
   d=2 (p=5): 实子域 = Q(√5)，黄金分割域 → 可逆（振荡）
   d=3 (p=7): 实子域 = Q(2cos(2π/7))，三次不可约扩张 → 不可逆
   ============================================================================ -/

/-- **代数扩张次数**：d = (p-1)/2。🔵 W1 严格 -/
def algebraicDegree (p : ℕ) (hp : p.Prime) : ℕ :=
  (p - 1) / 2

theorem degree_p3_eq_1 : algebraicDegree 3 Nat.prime_three = 1 := by
  unfold algebraicDegree; norm_num

theorem degree_p5_eq_2 : algebraicDegree 5 Nat.prime_five = 2 := by
  unfold algebraicDegree; norm_num

theorem degree_p7_eq_3 : algebraicDegree 7 Nat.prime_seven = 3 := by
  unfold algebraicDegree; norm_num

/-! ============================================================================
   §2. 各扩张次数的代数特征
   ============================================================================ -/

noncomputable def char_real_d1 : ℝ := 2 * Real.cos (2 * Real.pi / 3)

theorem char_real_d1_eq_minus_one : char_real_d1 = -1 := by
  unfold char_real_d1
  have h : Real.cos (2 * Real.pi / 3) = -1/2 := by
    have h1 : (2 : ℝ) * Real.pi / 3 = 2 * (Real.pi / 3) := by ring
    rw [h1]
    have h2 : Real.cos (2 * (Real.pi / 3)) = 2 * Real.cos (Real.pi / 3)^2 - 1 :=
      Real.cos_two_mul (Real.pi / 3)
    rw [h2, Real.cos_pi_div_three]
    ring
  rw [h]; ring

noncomputable def char_real_d2 : ℝ := 2 * Real.cos (2 * Real.pi / 5)

noncomputable def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

noncomputable def goldenConjugate : ℝ := (1 - Real.sqrt 5) / 2

noncomputable def char_real_d3 : ℝ := 2 * Real.cos (2 * Real.pi / 7)

theorem char_real_d3_cubic :
    char_real_d3^3 + char_real_d3^2 - 2 * char_real_d3 - 1 = 0 := by
  have h_eq : char_real_d3 = seventh_root_real_part 1 := by
    unfold char_real_d3 seventh_root_real_part
    congr 1 <;> push_cast <;> ring
  rw [h_eq]
  exact cos2pi7_cubic_equation

/-! ============================================================================
   §B. 桥接到 Foundation.k_out_Fin7 🔵 W1 严格

   这是本移植新增的关键桥接：
     theta_p 7 = 1 / (1 + k_out_Fin7)
   
   物理意义：
     - k_out_Fin7 是因果格的有效平均出度（Foundation §4.2）
     - theta_p 7 是素数 p=7 对应的物质密度参数原型
     - 二者通过同一个 2cos(2π/7) 共享代数来源
   
   这完成了从"基底素数 7"到"物理常数"的完整链条：
     MUST_HAVE ∋ 7 → k_out_Fin7 → G_unit = 1/k_out²（引力链）
                                → θ(7) = 1/(1+k_out)（密度参数链）
   ============================================================================ -/

/-! ============================================================================
   §3-§7 以下与 v12 完全一致，未做修改
   （内容包括：可逆性、不可逆性、结构形成窗口、素数排除、唯一性）
   ============================================================================ -/

/-! ============================================================================
   §3. 可逆性门槛定理
   ============================================================================ -/

def isReversible (p : ℕ) (hp : p.Prime) : Prop :=
  match algebraicDegree p hp with
  | 0 => True
  | 1 => True
  | 2 => True
  | _ => False

theorem p3_is_reversible : isReversible 3 Nat.prime_three := by
  unfold isReversible algebraicDegree; norm_num

theorem p5_is_reversible : isReversible 5 Nat.prime_five := by
  unfold isReversible algebraicDegree; norm_num

theorem p7_is_not_reversible : ¬ isReversible 7 Nat.prime_seven := by
  unfold isReversible algebraicDegree; norm_num

theorem reversibility_threshold (p : ℕ) (hp : p.Prime) (h_le2 : algebraicDegree p hp ≤ 2) :
    isReversible p hp := by
  have h : algebraicDegree p hp ≤ 2 := h_le2
  unfold isReversible
  interval_cases algebraicDegree p hp <;> exact trivial

/-! ============================================================================
   §4. 不可逆性门槛定理
   ============================================================================ -/

def isIrreversible (p : ℕ) (hp : p.Prime) : Prop :=
  algebraicDegree p hp ≥ 3

theorem p7_is_first_irreversible : isIrreversible 7 Nat.prime_seven := by
  unfold isIrreversible algebraicDegree; norm_num

theorem p7_irreversible : isIrreversible 7 Nat.prime_seven ∧
    ¬ isReversible 7 Nat.prime_seven := by
  exact ⟨p7_is_first_irreversible, p7_is_not_reversible⟩

theorem irreversibility_threshold :
    ∀ (p : ℕ) (hp : p.Prime), p > 2 → p < 7 →
      isReversible p hp := by
  intro p hp h_odd h_lt7
  interval_cases p
  · exact p3_is_reversible
  · exfalso; exact (by decide : ¬ Nat.Prime 4) hp
  · exact p5_is_reversible
  · exfalso; exact (by decide : ¬ Nat.Prime 6) hp

/-! ============================================================================
   §5. 结构形成窗口定理
   ============================================================================ -/

noncomputable def theta_p (p : ℕ) (hp : p.Prime) : ℝ :=
  1 / (2 + 2 * Real.cos (2 * Real.pi / p))

/-- **桥接定理（W1 严格）**：θ(7) = 1 / (1 + k_out_Fin7)。

    关联 Foundation §4.2 的 k_out_Fin7 和本文件的 theta_p 定义：
      theta_p p = 1 / (2 + 2cos(2π/p))
      k_out_Fin7 = 1 + 2cos(2π/7)
    所以 theta_p 7 = 1/(2 + 2cos(2π/7)) = 1/(1 + k_out_Fin7) ✓

    物理意义：引力量子 G_unit = 1/k_out² 和密度参数原型 θ(7)
    共享同一个代数根源——基底 p₄=7 通过 Fin 7 循环群的
    特征表示 cos(2π/7) 同时决定引力和密度的尺度。 -/
theorem theta_p7_eq_inv_one_plus_k_out :
    theta_p 7 Nat.prime_seven = 1 / (1 + CSQIT_W1.Foundation.k_out_Fin7) := by
  unfold theta_p CSQIT_W1.Foundation.k_out_Fin7
  norm_cast
  ring_nf

theorem theta_7_value : theta_p 7 Nat.prime_seven =
    1 / (2 + seventh_root_real_part 1) := by
  unfold theta_p seventh_root_real_part
  congr 1 <;> push_cast <;> ring

theorem theta_7_cubic :
    (theta_p 7 Nat.prime_seven)^3 -
    6 * (theta_p 7 Nat.prime_seven)^2 +
    5 * (theta_p 7 Nat.prime_seven) - 1 = 0 := by
  have hθ : theta_p 7 Nat.prime_seven = 1 / (2 + seventh_root_real_part 1) :=
    theta_7_value
  rw [hθ]
  have h1 : (seventh_root_real_part 1)^3 + (seventh_root_real_part 1)^2 -
    2 * (seventh_root_real_part 1) - 1 = 0 := cos2pi7_cubic_equation
  have h3 : (seventh_root_real_part 1)^3 =
    -((seventh_root_real_part 1)^2) + 2 * (seventh_root_real_part 1) + 1 := by linarith
  have h4 : (2 + seventh_root_real_part 1) ≠ 0 := by
    have h5 : 0 < seventh_root_real_part 1 := by
      have h6 : 2 * Real.pi / 7 < Real.pi / 3 := by linarith [Real.pi_pos]
      have h7 : Real.cos (2 * Real.pi / 7) > 1 / 2 := by
        have h8 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
        have h9 : Real.cos (2 * Real.pi / 7) > Real.cos (Real.pi / 3) := by
          apply Real.cos_lt_cos_of_nonneg_of_le_pi
          all_goals linarith [Real.pi_pos]
        linarith [h8, h9]
      dsimp only [seventh_root_real_part]
      linarith
    linarith
  field_simp [h4]
  rw [show (2 + seventh_root_real_part 1)^3 * 0 = 0 from by ring]
  have h_expand : (2 + seventh_root_real_part 1)^3 =
    8 + 12 * seventh_root_real_part 1 + 6 * (seventh_root_real_part 1)^2
      + (seventh_root_real_part 1)^3 := by ring
  rw [h_expand, h3]
  ring

/-! ----------------------------------------------------------------------------
   §5.1 cos(π/5) 的精确值
   ---------------------------------------------------------------------------- -/

theorem cos_pi_fifth_quadratic :
    4 * Real.cos (Real.pi / 5) ^ 2 - 2 * Real.cos (Real.pi / 5) - 1 = 0 := by
  have h1 : Real.sin (2 * (Real.pi / 5)) = Real.sin (3 * (Real.pi / 5)) := by
    have h2 : 2 * (Real.pi / 5) + 3 * (Real.pi / 5) = Real.pi := by ring
    have h3 : Real.sin (2 * (Real.pi / 5)) = Real.sin (Real.pi - 2 * (Real.pi / 5)) := by
      rw [Real.sin_pi_sub]
    have h4 : Real.pi - 2 * (Real.pi / 5) = 3 * (Real.pi / 5) := by ring
    rw [h4] at h3; exact h3
  have h_sin2 : Real.sin (2 * (Real.pi / 5)) =
      2 * Real.sin (Real.pi / 5) * Real.cos (Real.pi / 5) := by
    rw [Real.sin_two_mul] <;> ring
  have h_sin3 : Real.sin (3 * (Real.pi / 5)) =
      3 * Real.sin (Real.pi / 5) - 4 * Real.sin (Real.pi / 5) ^ 3 := by
    have h : ∀ (x : ℝ), Real.sin (3 * x) = 3 * Real.sin x - 4 * Real.sin x ^ 3 := by
      intro x
      calc
        Real.sin (3 * x) = Real.sin (2 * x + x) := by ring_nf
        _ = Real.sin (2 * x) * Real.cos x + Real.cos (2 * x) * Real.sin x := by rw [Real.sin_add]
        _ = (2 * Real.sin x * Real.cos x) * Real.cos x +
              (2 * Real.cos x ^ 2 - 1) * Real.sin x := by
            rw [Real.sin_two_mul, Real.cos_two_mul] <;> ring
        _ = 4 * Real.sin x * Real.cos x ^ 2 - Real.sin x := by ring
        _ = 4 * Real.sin x * (1 - Real.sin x ^ 2) - Real.sin x := by
            have h2 : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
              have h3 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
              linarith
            rw [h2] <;> ring
        _ = 3 * Real.sin x - 4 * Real.sin x ^ 3 := by ring
    exact h (Real.pi / 5)
  rw [h_sin2, h_sin3] at h1
  have h_pos : 0 < Real.sin (Real.pi / 5) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
  have h_eq : 2 * Real.sin (Real.pi / 5) * Real.cos (Real.pi / 5) =
      3 * Real.sin (Real.pi / 5) - 4 * Real.sin (Real.pi / 5) ^ 3 := h1
  have h_eq2 : 2 * Real.cos (Real.pi / 5) = 3 - 4 * Real.sin (Real.pi / 5) ^ 2 := by
    apply (mul_right_inj' (ne_of_gt h_pos)).mp; linarith
  have h_sq : Real.sin (Real.pi / 5) ^ 2 = 1 - Real.cos (Real.pi / 5) ^ 2 := by
    have h : Real.sin (Real.pi / 5) ^ 2 + Real.cos (Real.pi / 5) ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq (Real.pi / 5); linarith
  rw [h_sq] at h_eq2; linarith

theorem cos_pi_fifth_value :
    Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := by
  have h1 : 4 * Real.cos (Real.pi / 5) ^ 2 - 2 * Real.cos (Real.pi / 5) - 1 = 0 :=
    cos_pi_fifth_quadratic
  have h_pos : 0 < Real.cos (Real.pi / 5) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have h2 : (Real.cos (Real.pi / 5) - (1 + Real.sqrt 5) / 4) *
      (Real.cos (Real.pi / 5) - (1 - Real.sqrt 5) / 4) = 0 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  have h3 : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 ∨
      Real.cos (Real.pi / 5) = (1 - Real.sqrt 5) / 4 := by
    have h4 := eq_zero_or_eq_zero_of_mul_eq_zero h2
    cases h4 with
    | inl h4 => left; linarith
    | inr h4 => right; linarith
  cases h3 with
  | inl h3 => exact h3
  | inr h3 =>
    have h5 : Real.sqrt 5 > 1 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    have h6 : (1 - Real.sqrt 5) / 4 < 0 := by linarith
    rw [h3] at h_pos; linarith

/-! ----------------------------------------------------------------------------
   §5.2 d=2 特征实数与黄金分割关系
   ---------------------------------------------------------------------------- -/

theorem char_real_d2_quadratic :
    char_real_d2^2 + char_real_d2 - 1 = 0 := by
  unfold char_real_d2
  have h_cos : Real.cos (2 * Real.pi / 5) = 2 * Real.cos (Real.pi / 5)^2 - 1 := by
    have h := Real.cos_two_mul (Real.pi / 5)
    rw [show 2 * (Real.pi / 5) = 2 * Real.pi / 5 from by ring] at h
    exact h
  rw [h_cos, cos_pi_fifth_value]
  have h_sqrt : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h_sqrt]

theorem char_real_d2_eq_neg_golden_conjugate :
    char_real_d2 = -goldenConjugate := by
  unfold char_real_d2 goldenConjugate
  have h_cos : Real.cos (2 * Real.pi / 5) = 2 * Real.cos (Real.pi / 5)^2 - 1 := by
    have h := Real.cos_two_mul (Real.pi / 5)
    rw [show 2 * (Real.pi / 5) = 2 * Real.pi / 5 from by ring] at h
    exact h
  rw [h_cos, cos_pi_fifth_value]
  have h_sqrt : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)
  linarith [h_sqrt]

/-! ----------------------------------------------------------------------------
   §5.3 p ≥ 11 排除：θ(p) < 0.28
   ---------------------------------------------------------------------------- -/

theorem cos_pi_fifth_gt_eleven_fourteenths :
    Real.cos (Real.pi / 5) > 11 / 14 := by
  rw [cos_pi_fifth_value]
  have h1 : Real.sqrt 5 > 15 / 7 := by
    nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  linarith

theorem two_pi_over_p_lt_pi_fifth {p : ℕ} (h : p ≥ 11) :
    2 * Real.pi / (p : ℝ) < Real.pi / 5 := by
  have h1 : (p : ℝ) ≥ 11 := by exact_mod_cast h
  have h2 : 2 * Real.pi / (p : ℝ) ≤ 2 * Real.pi / 11 := by
    gcongr <;> linarith
  have h3 : (2 * Real.pi / 11 : ℝ) < Real.pi / 5 := by
    linarith [Real.pi_pos]
  linarith

theorem cos_two_pi_over_p_gt {p : ℕ} (hp : p ≥ 11) :
    Real.cos (2 * Real.pi / (p : ℝ)) > 11 / 14 := by
  have h1 : 0 ≤ 2 * Real.pi / (p : ℝ) := by positivity
  have h2 : 2 * Real.pi / (p : ℝ) < Real.pi / 5 := two_pi_over_p_lt_pi_fifth hp
  have h3 : 2 * Real.pi / (p : ℝ) < Real.pi := by linarith [Real.pi_pos]
  have h4 : Real.cos (2 * Real.pi / (p : ℝ)) > Real.cos (Real.pi / 5) := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi <;> linarith [Real.pi_pos]
  have h5 : Real.cos (Real.pi / 5) > 11 / 14 := cos_pi_fifth_gt_eleven_fourteenths
  linarith

theorem theta_p_upper_bound {p : ℕ} (hp : Nat.Prime p)
    (h_denom_lower : 2 + 2 * Real.cos (2 * Real.pi / (p : ℝ)) > 25 / 7) :
    theta_p p hp < 7 / 25 := by
  have h_pos : 0 < 2 + 2 * Real.cos (2 * Real.pi / (p : ℝ)) := by linarith
  have h_pos2 : (0 : ℝ) < 25 / 7 := by norm_num
  unfold theta_p
  have h : (1 : ℝ) / (2 + 2 * Real.cos (2 * Real.pi / (p : ℝ))) < 1 / (25 / 7) := by
    apply one_div_lt_one_div_of_lt h_pos2 h_denom_lower
  have h2 : (1 : ℝ) / (25 / 7) = 7 / 25 := by norm_num
  rw [h2] at h
  exact h

theorem prime_exclusion_upper (p : ℕ) (hp : Nat.Prime p) (h_ge11 : p ≥ 11) :
    theta_p p hp < 0.28 := by
  have h1 : Real.cos (2 * Real.pi / (p : ℝ)) > 11 / 14 := cos_two_pi_over_p_gt h_ge11
  have h2 : 2 + 2 * Real.cos (2 * Real.pi / (p : ℝ)) > 25 / 7 := by linarith
  have h3 : theta_p p hp < 7 / 25 := theta_p_upper_bound hp h2
  have h4 : (7 / 25 : ℝ) = 0.28 := by norm_num
  rw [h4] at h3; exact h3

/-! ----------------------------------------------------------------------------
   §5.4 p = 3, p = 5 排除：θ(p) > 0.33
   ---------------------------------------------------------------------------- -/

theorem theta_p3_eq_one : theta_p 3 Nat.prime_three = 1 := by
  unfold theta_p
  have h3 : Real.cos (2 * Real.pi / (3 : ℝ)) = -1 / 2 := by
    have h_eq : (2 * Real.pi / (3 : ℝ)) = 2 * (Real.pi / 3) := by ring
    rw [h_eq]
    have h2 : Real.cos (2 * (Real.pi / 3)) = 2 * Real.cos (Real.pi / 3) ^ 2 - 1 :=
      Real.cos_two_mul (Real.pi / 3)
    rw [h2, Real.cos_pi_div_three] <;> ring
  have h_cast : (3 : ℝ) = ↑(3 : ℕ) := by norm_num
  have h4 : Real.cos (2 * Real.pi / ↑(3 : ℕ)) = -1 / 2 := by
    rw [←h_cast]
    exact h3
  rw [h4]
  norm_num

theorem theta_p3_gt : theta_p 3 Nat.prime_three > 0.33 := by
  rw [theta_p3_eq_one] <;> norm_num

theorem cos_two_pi_five_lt_cos_pi3 :
    Real.cos (2 * Real.pi / 5) < Real.cos (Real.pi / 3) := by
  apply Real.cos_lt_cos_of_nonneg_of_le_pi <;> linarith [Real.pi_pos]

theorem theta_p5_gt_third :
    theta_p 5 Nat.prime_five > 1 / 3 := by
  have h1 : Real.cos (2 * Real.pi / 5) < Real.cos (Real.pi / 3) :=
    cos_two_pi_five_lt_cos_pi3
  have h2 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
  have h3 : Real.cos (2 * Real.pi / 5) < 1 / 2 := by linarith
  have h4 : 0 < 2 + 2 * Real.cos (2 * Real.pi / 5) := by
    have h5 : Real.cos (2 * Real.pi / 5) > 0 := by
      apply Real.cos_pos_of_mem_Ioo; constructor <;> linarith [Real.pi_pos]
    linarith
  unfold theta_p
  have h6 : (1 : ℝ) / (2 + 2 * Real.cos (2 * Real.pi / 5)) > 1 / 3 := by
    apply one_div_lt_one_div_of_lt <;> linarith
  exact h6

theorem theta_p5_gt : theta_p 5 Nat.prime_five > 0.33 := by
  have h1 : theta_p 5 Nat.prime_five > 1 / 3 := theta_p5_gt_third
  have h2 : (1 / 3 : ℝ) > 0.33 := by norm_num
  linarith

/-! ----------------------------------------------------------------------------
   §5.5 cos(2π/7) 的精确有理界 → θ(7) ∈ (0.28, 0.33)
   ---------------------------------------------------------------------------- -/

theorem cos_two_pi_seventh_lt_eleven_fourteenths :
    Real.cos (2 * Real.pi / 7) < 11 / 14 := by
  have h_le_pi : 2 * Real.pi / 7 ≤ Real.pi := by linarith [Real.pi_pos]
  have h1 : Real.pi / 4 < 2 * Real.pi / 7 := by
    have : (2:ℝ) / 7 > 1 / 4 := by norm_num
    linarith [Real.pi_pos]
  have h_nonneg : 0 ≤ Real.pi / 4 := by linarith [Real.pi_pos]
  have h_cos : Real.cos (2 * Real.pi / 7) < Real.cos (Real.pi / 4) := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    · exact h_nonneg
    · linarith [h_le_pi]
    · linarith [h1]
  have h_cos_pi4 : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  have h_sqrt : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [h_cos, h_cos_pi4, h_sqrt, Real.sqrt_nonneg 2]

theorem cos_two_pi_seventh_gt_seven_thirty_thirds :
    Real.cos (2 * Real.pi / 7) > 17 / 33 := by
  have h1 : 2 * Real.pi / 7 < 3 * Real.pi / 10 := by
    have : (2:ℝ) / 7 < 3 / 10 := by norm_num
    linarith [Real.pi_pos]
  have h_nonneg : 0 ≤ 2 * Real.pi / 7 := by positivity
  have h_le_pi : 3 * Real.pi / 10 ≤ Real.pi := by linarith [Real.pi_pos]
  have h_cos : Real.cos (2 * Real.pi / 7) > Real.cos (3 * Real.pi / 10) := by
    apply Real.cos_lt_cos_of_nonneg_of_le_pi
    · exact h_nonneg
    · linarith [h_le_pi]
    · linarith [h1]
  have h_sin : Real.cos (3 * Real.pi / 10) = Real.sin (Real.pi / 5) := by
    have h_eq : 3 * Real.pi / 10 = Real.pi / 2 - Real.pi / 5 := by ring
    rw [h_eq]; exact Real.cos_pi_div_two_sub (Real.pi / 5)
  have h_cos2 : Real.cos (2 * Real.pi / 7) > Real.sin (Real.pi / 5) := by
    linarith [h_cos, h_sin]
  have h_sin_pos : 0 < Real.sin (Real.pi / 5) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  have h_17_pos : (0 : ℝ) < 17 / 33 := by norm_num
  have h_cos_pi5 : Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 4 := cos_pi_fifth_value
  have h_sin_sq : Real.sin (Real.pi / 5)^2 = (10 - 2 * Real.sqrt 5) / 16 := by
    have h_sc : Real.sin (Real.pi / 5)^2 + Real.cos (Real.pi / 5)^2 = 1 :=
      Real.sin_sq_add_cos_sq (Real.pi / 5)
    rw [h_cos_pi5] at h_sc
    have h_sqrt5 : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)
    nlinarith [h_sqrt5]
  have h_sq_gt : Real.sin (Real.pi / 5)^2 > (17 / 33 : ℝ)^2 := by
    rw [h_sin_sq]
    have h_sqrt5 : (Real.sqrt 5)^2 = 5 := Real.sq_sqrt (by norm_num)
    have h_sqrt5_nn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    nlinarith [h_sqrt5, h_sqrt5_nn]
  have h_sin_gt_17 : Real.sin (Real.pi / 5) > 17 / 33 := by
    nlinarith [h_sin_pos, h_17_pos, h_sq_gt,
      sq_nonneg (Real.sin (Real.pi / 5) - 17 / 33),
      sq_nonneg (Real.sin (Real.pi / 5) + 17 / 33)]
  linarith [h_cos2, h_sin_gt_17]

theorem theta_7_gt_lower_bound :
    theta_p 7 Nat.prime_seven > 0.28 := by
  have h_cos : Real.cos (2 * Real.pi / 7) < 11 / 14 := cos_two_pi_seventh_lt_eleven_fourteenths
  have h_denom : 2 + 2 * Real.cos (2 * Real.pi / 7) < 25 / 7 := by linarith
  have h_denom_pos : 0 < 2 + 2 * Real.cos (2 * Real.pi / 7) := by
    have : 0 < Real.cos (2 * Real.pi / 7) := by
      apply Real.cos_pos_of_mem_Ioo; constructor <;> linarith [Real.pi_pos]
    linarith
  have h_25_7_pos : (0 : ℝ) < 25 / 7 := by norm_num
  unfold theta_p
  have h_inv : 1 / (25 / 7) < 1 / (2 + 2 * Real.cos (2 * Real.pi / 7)) := by
    apply one_div_lt_one_div_of_lt h_denom_pos h_denom
  have h_eq : (1 / (25 / 7) : ℝ) = 7 / 25 := by norm_num
  have h_eq2 : (7 / 25 : ℝ) = 0.28 := by norm_num
  linarith

theorem theta_7_lt_upper_bound :
    theta_p 7 Nat.prime_seven < 0.33 := by
  have h_cos : Real.cos (2 * Real.pi / 7) > 17 / 33 := cos_two_pi_seventh_gt_seven_thirty_thirds
  have h_denom : 2 + 2 * Real.cos (2 * Real.pi / 7) > 100 / 33 := by linarith
  have h_denom_pos : 0 < 2 + 2 * Real.cos (2 * Real.pi / 7) := by
    have : 0 < Real.cos (2 * Real.pi / 7) := by
      apply Real.cos_pos_of_mem_Ioo; constructor <;> linarith [Real.pi_pos]
    linarith
  have h_100_33_pos : (0 : ℝ) < 100 / 33 := by norm_num
  unfold theta_p
  have h_inv : 1 / (2 + 2 * Real.cos (2 * Real.pi / 7)) < 1 / (100 / 33) := by
    apply one_div_lt_one_div_of_lt h_100_33_pos h_denom
  have h_eq : (1 / (100 / 33) : ℝ) = 33 / 100 := by norm_num
  have h_eq2 : (33 / 100 : ℝ) = 0.33 := by norm_num
  linarith

/-! ============================================================================
   §6-§7. 素数排除与 Fin 7 唯一性综合定理
   ============================================================================ -/

def IsStructureForming (θ : ℝ) : Prop := θ > 0.28 ∧ θ < 0.33

theorem prime_exclusion_theorem :
    ∀ (p : ℕ) (hp : Nat.Prime p), p > 2 → p ≠ 7 →
      IsStructureForming (theta_p p hp) → False := by
  intro p hp h_odd h_ne7 h_sf
  have h_lower : theta_p p hp > 0.28 := h_sf.1
  have h_upper : theta_p p hp < 0.33 := h_sf.2
  by_cases h_lt7 : p < 7
  · have h_lo : 3 ≤ p := by omega
    have h_hi : p ≤ 6 := by omega
    interval_cases p
    · have h_contra : theta_p 3 Nat.prime_three > 0.33 := theta_p3_gt; linarith
    · exfalso; exact absurd hp (by decide)
    · have h_contra : theta_p 5 Nat.prime_five > 0.33 := theta_p5_gt; linarith
    · exfalso; exact absurd hp (by decide)
  · have h_ge7 : p ≥ 7 := by omega
    have h_ge11 : p ≥ 11 := by
      by_contra h
      have h_lt11 : p < 11 := by omega
      have h7 : p = 7 ∨ p = 8 ∨ p = 9 ∨ p = 10 := by omega
      rcases h7 with (h7 | h7 | h7 | h7)
      · exact h_ne7 h7
      · exfalso; exact (by decide : ¬ Nat.Prime 8) (by rwa [h7] at hp)
      · exfalso; exact (by decide : ¬ Nat.Prime 9) (by rwa [h7] at hp)
      · exfalso; exact (by decide : ¬ Nat.Prime 10) (by rwa [h7] at hp)
    have h_contra : theta_p p hp < 0.28 := prime_exclusion_upper p hp h_ge11
    linarith

theorem irreversible_implies_ge_7 (p : ℕ) (hp : p.Prime) (h_odd : p > 2)
    (h_irr : isIrreversible p hp) : p ≥ 7 := by
  unfold isIrreversible algebraicDegree at h_irr
  have h : p - 1 ≥ 6 := by omega
  omega

theorem seven_is_minimal_irreversible :
    ∀ (p : ℕ) (hp : p.Prime), p > 2 →
      isIrreversible p hp → p ≥ 7 := by
  intro p hp h_odd h_irr
  exact irreversible_implies_ge_7 p hp h_odd h_irr

theorem fin7_unique_satisfying_both_constraints :
    ∀ (p : ℕ) (hp : p.Prime), p > 2 →
      isIrreversible p hp →
      IsStructureForming (theta_p p hp) →
      p = 7 := by
  intro p hp h_odd h_irr h_sf
  have h_ge7 : p ≥ 7 := seven_is_minimal_irreversible p hp h_odd h_irr
  by_contra h_ne7
  have h_contra : IsStructureForming (theta_p p hp) → False :=
    prime_exclusion_theorem p hp h_odd h_ne7
  exact h_contra h_sf

theorem fin7_uniqueness : ∃! (p : ℕ), ∃ hp : p.Prime,
    p > 2 ∧ isIrreversible p hp ∧ IsStructureForming (theta_p p hp) := by
  refine ⟨7, ?_, ?_⟩
  · refine ⟨Nat.prime_seven, by norm_num, p7_is_first_irreversible,
      ⟨theta_7_gt_lower_bound, theta_7_lt_upper_bound⟩⟩
  · rintro y ⟨hy_prime, hy_odd, hy_irr, hy_sf⟩
    exact fin7_unique_satisfying_both_constraints y hy_prime hy_odd hy_irr hy_sf

end CSQIT_W1.Fin7Uniqueness
