/- ================================================================================
CSQIT — 「时间＝变化的刻度」：差分恒等式与平移不封闭
文件: CSQIT_TimeScale/Flow.lean

A 部分（差分）：`t_n = 2πn/(n+1)`，则
    t_{n+1} − t_n = 2π / ((n+1)(n+2))          (projectiveScale_succ_sub)
                  = g_{n²+3n+1}                (succ_sub_eq_gap,  g_m = 2π/(m+1))
                  = g_n · g_{n+1} / (2π)       (succ_sub_eq_gap_mul)
  二阶差分同样能用缺口表示：
    t_{n+2} − 2t_{n+1} + t_n = − g_n · g_{n+1} · g_{n+2} / (2π²)
                                              (second_diff_eq_gap)

B 部分（平移）：`t ↦ t + τ` 在 `{t_n}` 上不封闭。
    no_nontrivial_translation : τ ≠ 0 时必存在 n，使 t_n + τ 不在 {t_m} 中。

层级：W1/A 档（零新增 axiom，零 sorry）
================================================================================ -/

import CSQIT_TimeScale.GapScale

namespace CSQIT.TimeScale

open CSQIT_W1.Foundation
open Filter

/-! ============================================================================
   §A. 一阶差分
   ============================================================================ -/

/-- **一阶差分**（A 档）：`t_{n+1} − t_n = 2π / ((n+1)(n+2))`。
    分母来自 `(n+1)² − n(n+2) = 1`。 -/
theorem projectiveScale_succ_sub (n : ℕ) :
    projectiveScale (n + 1) - projectiveScale n =
      2 * Real.pi / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  unfold projectiveScale
  push_cast
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

/-- **差分等于某个缺口**（A 档）：`t_{n+1} − t_n = g_{n²+3n+1}`。
    索引 `n²+3n+1 = (n+1)(n+2) − 1` 对一切 `n : ℕ` 都是自然数，
    **不需要 `n ≥ 1` 或任何附加限制**。 -/
theorem succ_sub_eq_gap (n : ℕ) :
    projectiveScale (n + 1) - projectiveScale n = gap (n ^ 2 + 3 * n + 1) := by
  rw [projectiveScale_succ_sub]
  unfold gap
  congr 1
  push_cast
  ring

/-- **差分等于相邻两个缺口的归一化乘积**（A 档）：
    `t_{n+1} − t_n = g_n · g_{n+1} / (2π)`。 -/
theorem succ_sub_eq_gap_mul (n : ℕ) :
    projectiveScale (n + 1) - projectiveScale n =
      gap n * gap (n + 1) / (2 * Real.pi) := by
  rw [projectiveScale_succ_sub]
  unfold gap
  push_cast
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  have hp : (2 * Real.pi) ≠ 0 := ne_of_gt (show (0 : ℝ) < 2 * Real.pi by positivity)
  field_simp
  ring

/-- **差分等于缺口乘积（直接套 `gap_mul` 的另证）**（A 档）：
    同一恒等式，但不展开 `gap`，而是取 `gap_mul` 的 `a = n+1, b = n+2`。
    `gap_mul` 的前提 `1 ≤ a`、`1 ≤ b` 在此自动满足，**无需 `n ≥ 1`**。 -/
theorem succ_sub_eq_gap_mul_via_gap_mul (n : ℕ) :
    projectiveScale (n + 1) - projectiveScale n =
      gap n * gap (n + 1) / (2 * Real.pi) := by
  rw [succ_sub_eq_gap]
  have hpos : 1 ≤ (n + 1) * (n + 2) :=
    Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos (n + 1))
  have h := gap_mul (n + 1) (n + 2) (by omega) (by omega)
  have e1 : (n + 1) * (n + 2) - 1 = n ^ 2 + 3 * n + 1 := by
    rw [Nat.sub_eq_iff_eq_add hpos]
    ring
  have e2 : (n + 1) - 1 = n := by omega
  have e3 : (n + 2) - 1 = n + 1 := by omega
  rw [e1, e2, e3] at h
  have hp : (2 * Real.pi) ≠ 0 := ne_of_gt (show (0 : ℝ) < 2 * Real.pi by positivity)
  rw [eq_div_iff hp]
  linear_combination h

/-! ============================================================================
   §A'. 二阶差分
   ============================================================================ -/

/-- **二阶差分**（A 档）：`t_{n+2} − 2t_{n+1} + t_n = −g_n · g_{n+1} · g_{n+2} / (2π²)`。
    即 `t` 是凹的，且二阶差分是**三个连续缺口之积**（带负号）。
    这条否掉了"二阶差分不能用缺口表示"的可能。 -/
theorem second_diff_eq_gap (n : ℕ) :
    projectiveScale (n + 2) - 2 * projectiveScale (n + 1) + projectiveScale n =
      -(gap n * gap (n + 1) * gap (n + 2)) / (2 * Real.pi ^ 2) := by
  unfold projectiveScale gap
  push_cast
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  have h3 : ((n : ℝ) + 3) ≠ 0 := by positivity
  have hp : (2 * Real.pi) ≠ 0 := ne_of_gt (show (0 : ℝ) < 2 * Real.pi by positivity)
  field_simp
  ring

/-! ============================================================================
   §B. 平移不封闭
   ============================================================================ -/

/-- **正向平移必然逃出 `{t_n}`**（A 档）：对任意 `τ > 0`，存在 `n`
    使 `t_n + τ` 不是任何 `t_m`。
    证明只用既有极限 `projective_scale_tendsto_two_pi` 与上界
    `projectiveScale_lt_two_pi`：`t_n → 2π`，故取 `t_n > 2π − τ` 即可。 -/
theorem shift_escapes (τ : ℝ) (hτ : 0 < τ) :
    ∃ n : ℕ, ∀ m : ℕ, projectiveScale n + τ ≠ projectiveScale m := by
  have hlt : 2 * Real.pi - τ < 2 * Real.pi := by linarith
  have hev : ∀ᶠ n : ℕ in atTop, 2 * Real.pi - τ < projectiveScale n :=
    projective_scale_tendsto_two_pi.eventually (eventually_gt_nhds hlt)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun m hm => ?_⟩
  have h1 : 2 * Real.pi - τ < projectiveScale N := hN N le_rfl
  have h2 : projectiveScale m < 2 * Real.pi := projectiveScale_lt_two_pi m
  linarith

/-- **唯一的"自同构"是恒等**（A 档）：若 `τ ≠ 0`，则平移 `t ↦ t + τ`
    一定把某个 `t_n` 抛出 `{t_m}`。
    - `τ > 0`：由 `shift_escapes`（追上 2π 后越界）。
    - `τ < 0`：取 `n = 0`，`t_0 + τ = τ < 0 ≤ t_m`。
    故 `{t_n}` 上没有非平凡的时间平移对称性，Noether 的平移→能量通道在此断裂。 -/
theorem no_nontrivial_translation (τ : ℝ) (hτ : τ ≠ 0) :
    ∃ n : ℕ, ∀ m : ℕ, projectiveScale n + τ ≠ projectiveScale m := by
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · refine ⟨0, fun m hm => ?_⟩
    have h0 : projectiveScale 0 = 0 := by
      unfold projectiveScale
      ring_nf
    have hmn : 0 ≤ projectiveScale m := projectiveScale_nonneg m
    linarith
  · exact shift_escapes τ hpos

end CSQIT.TimeScale
