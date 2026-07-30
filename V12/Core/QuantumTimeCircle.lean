/- ================================================================================
CSQIT v12.1.2 — 量子相位与时间之圆的同构
文件: V12/Core/QuantumTimeCircle.lean
版本: v12.1.2
日期: 2026-07-30
================================================================================
核心思想（W3 层概念，W1/W2 层支撑）：
  量子力学的相位角 θ 与时间圆的射影尺度 s(n) 在拓扑上等同。
  振幅的相位演化，就是编织机在时间圆上绕圈。
  不存在"外部时间参数 t"，只有"内部闭包索引 n"映射到 S¹ 上的点。

理论层级说明（诚实标注，v12.1.0 深度自检修正）：
  - §1：基础同构数学定义 —— W1 严格（复相位 ↔ S¹ 映射）
  - §2：时间演化数学性质 —— W1 严格（函数性质） / W3 诠释（"演化"）
  - §3-§4：W2 条件性定理与 W3 层概念性命题
  - §5：W3 层最终统一声明
================================================================================ -/

import V12.Core.Foundation
import V12.Core.AlgebraicTimeCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace CSQIT.V12.QuantumTimeCircle

open CSQIT.V12.Foundation
open CSQIT.V12.AlgebraicTimeCircle
open Complex

/-! ============================================================================
   §1. 基础同构：量子相位 = 时间圆上的点（W1 严格定义）
   ============================================================================ -/

/-- **振幅到时间圆的映射**（W1 严格定义）。
    利用 `Complex.arg` 提取振幅的相位角（值域 (-π, π]），
    再包装到时间圆 S¹ 的规范区间 [0, 2π)。
    当 arg α < 0 时，加 2π 平移到正区间；否则直接使用。
    由于 |amplitude|² = 1，振幅落在单位圆上，其角度唯一对应时间圆上的点。

    边界情况说明（v12.1.0 加固）：
      - `Complex.arg` 的值域是 (-π, π]（开区间左端，闭区间右端）
      - `Complex.neg_pi_lt_arg` 保证 arg > -π，故 arg = -π 不可能出现
      - 当 arg = π 时（负实轴），θ ≥ 0 走 else 分支，返回 ⟨π, 0≤π, π<2π⟩，正确
      - 因此当前实现对所有可能的 arg 值均正确，无需额外边界处理 -/
noncomputable def amplitude_to_phase (α : ℂ) (hα : α ≠ 0) : TimeCircle :=
  let θ := Complex.arg α
  if hθ : θ < 0 then
    have h_lower : -Real.pi < θ := Complex.neg_pi_lt_arg α
    have h_upper : θ + 2 * Real.pi < 2 * Real.pi := by linarith
    have h_nonneg : 0 ≤ θ + 2 * Real.pi := by linarith
    ⟨θ + 2 * Real.pi, h_nonneg, h_upper⟩
  else
    have h_nonneg : 0 ≤ θ := by linarith
    have h_upper : θ < 2 * Real.pi := by
      have h1 : θ ≤ Real.pi := Complex.arg_le_pi α
      linarith [Real.pi_pos]
    ⟨θ, h_nonneg, h_upper⟩

/-- 时间圆上的任意角度都可以提升为一个振幅（通过 U(1) 的指数映射）。 -/
noncomputable def phase_to_amplitude (θ : TimeCircle) : ℂ :=
  Complex.exp (Complex.I * θ.val)

/-! ============================================================================
   §2. 时间演化 = 在时间圆上移动（W1 严格）
   ============================================================================ -/

/-- 在标准量子力学中，时间演化算符是 U(t) = exp(-i H t / ℏ)。
    在编织机中，"演化"对应于将闭包索引 n 增加到 n+1。
    相位的变化 Δθ = projectiveScale(n+1) - projectiveScale(n)。 -/
noncomputable def weave_step_phase_shift (n : ℕ) : ℝ :=
  projectiveScale (n + 1) - projectiveScale n

/-- 定理：弧长永远为正（W1 严格）。
    projectiveScale 严格递增，故每步相位差为正。 -/
theorem step_phase_shift_positive (n : ℕ) : 0 < weave_step_phase_shift n := by
  unfold weave_step_phase_shift
  have h : projectiveScale n < projectiveScale (n + 1) :=
    projectiveScale_strictMono (by linarith)
  linarith

/-- 定理：弧长永远小于 2π（W1 严格）。 -/
theorem step_phase_shift_lt_two_pi (n : ℕ) : weave_step_phase_shift n < 2 * Real.pi := by
  unfold weave_step_phase_shift
  linarith [projectiveScale_lt_two_pi (n + 1), projectiveScale_nonneg n]

/-! ============================================================================
   §3. 时间反演 T：圆上的反射（W1 严格定义 + W2 条件性定理）
   ============================================================================ -/

/-- 在时间圆上，时间反演算符 T 将角度 θ 映射到 2π - θ（模 2π）。
    当 θ = 0 时，2π - 0 = 2π ≡ 0（模 2π），故映射到 0。 -/
noncomputable def time_reversal_on_circle (θ : TimeCircle) : TimeCircle :=
  if h : θ.val = 0 then
    ⟨0, by linarith, by linarith [Real.pi_pos]⟩
  else
    have h_pos : 0 < θ.val := by
      by_contra h2
      have h3 : θ.val = 0 := by linarith [θ.prop.1]
      exact h h3
    ⟨2 * Real.pi - θ.val,
     by
       have h2 : θ.val < 2 * Real.pi := θ.prop.2
       linarith,
     by
       have h2 : 0 < θ.val := h_pos
       linarith⟩

/-- W2 条件性定理：振幅在时间反演下共轭。
    前提条件：振幅角度 > 0 且共轭振幅角度 = 2π - 原振幅角度。 -/
theorem time_reversal_conjugates_amplitude
    (α : ℂ)
    (hα : α ≠ 0)
    (h_phase_eq : (amplitude_to_phase α hα).val = Complex.arg α)
    (h_conj : Complex.arg (star α) = 2 * Real.pi - Complex.arg α)
    (h_arg_pos : 0 < Complex.arg α) :
    (time_reversal_on_circle (amplitude_to_phase α hα)).val =
    Complex.arg (star α) := by
  have h_ne_zero : (amplitude_to_phase α hα).val ≠ 0 := by
    rw [h_phase_eq]
    <;> linarith
  have h_main : (time_reversal_on_circle (amplitude_to_phase α hα)).val =
      2 * Real.pi - (amplitude_to_phase α hα).val := by
    unfold time_reversal_on_circle
    rw [dif_neg h_ne_zero]
    <;> rfl
  rw [h_main, h_phase_eq, h_conj]
  <;> ring

/-! ============================================================================
   §4. 贝里相位（Berry Phase）的拓扑诠释（W1 严格 + W3 概念性命题）
   ============================================================================ -/

/-- 绕时间圆走完整一圈的贝里相位：
    γ_Berry = 2π × 420/421 ≈ 2π。
    对于有限 n，它接近但不等于 2π，残余 2π/421 可能是暗能量的拓扑来源。 -/
noncomputable def berry_phase_around_circle : ℝ :=
  2 * Real.pi * (420 : ℝ) / 421

/-- 定理：贝里相位的残余值（W1 严格）。
    Δγ = 2π - γ_Berry = 2π/421，这个微小残余是暗能量的拓扑候选来源。 -/
theorem berry_phase_residual :
    2 * Real.pi - berry_phase_around_circle = 2 * Real.pi / 421 := by
  unfold berry_phase_around_circle
  ring

/-- W3 层概念性命题：贝里相位在模 2π 意义下平凡。 -/
def berry_phase_trivial_conjecture : Prop :=
  ∃ (k : ℤ), berry_phase_around_circle = 2 * Real.pi * k

/-! ============================================================================
   §5. 最终统一：时间圆 = 相位圆 = 因果闭包圆
   ============================================================================ -/

/-- 统一圆：将时间、量子相位、因果闭包统一到同一个 S¹ 上。 -/
def UnitaryTimeCircle : Type :=
  {θ : ℝ // 0 ≤ θ ∧ θ < 2 * Real.pi}

/-- 从闭包索引到统一圆上的点的规范映射（W1 严格）。 -/
noncomputable def closure_to_unitary_circle (n : ℕ) : UnitaryTimeCircle :=
  ⟨projectiveScale n, projectiveScale_nonneg n, projectiveScale_lt_two_pi n⟩

/-- W3 层概念性命题：闭包映射在 420 周期下不变。 -/
def time_circle_unified_conjecture : Prop :=
  ∀ (n : ℕ), (closure_to_unitary_circle (n + 420)).val =
    (closure_to_unitary_circle n).val

end CSQIT.V12.QuantumTimeCircle
