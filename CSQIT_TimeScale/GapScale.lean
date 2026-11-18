/- ================================================================================
CSQIT — 「尺度藏在缺口里」：B 部分的判定落码
文件: CSQIT_TimeScale/GapScale.lean

时间坐标 `t_n = 2πn/(n+1)` 是维度式的（有序、无乘法，见 CSQIT_TimeScale/Verdict.lean）。
本文件检验它的补集（缺口）`g_n = 2π − t_n = 2π/(n+1)` 是否携带尺度结构：

  1. `gap_mul`：`g_{ab-1} · 2π = g_{a-1} · g_{b-1}`（用户猜想的精确形式）
  2. `gapUnit_mul`：归一化缺口 `k ↦ 1/k` 是 ({1,2,3,…}, ·) 到 `Scale` 的乘法同态
  3. `gapReversal_projectiveScale`：`t ↦ 2π²/(2π−t)` 在 `{t_n}` 上有闭式 `π(n+1)`
  4. `gapReversal_out_of_range`：该反演（n ≥ 1 时）把 `t_n` 抛出 `{t_n}`，不闭合

层级：A 档（零新增 axiom，零 sorry）
================================================================================ -/

import CSQIT_TimeScale.Verdict

namespace CSQIT.TimeScale

open CSQIT_W1.Foundation

/-- **缺口**：`g(n) = 2π/(n+1)`，即时间坐标到 2π 的距离。 -/
noncomputable def gap (n : ℕ) : ℝ := 2 * Real.pi / ((n : ℝ) + 1)

/-- 缺口为正（A 档）。 -/
theorem gap_pos (n : ℕ) : 0 < gap n := by
  unfold gap
  positivity

/-- 缺口等于 `2π` 减时间坐标（A 档，即 `deficit_eq` 的重述）。 -/
theorem gap_eq_deficit (n : ℕ) : gap n = 2 * Real.pi - projectiveScale n := by
  unfold gap
  exact (deficit_eq n).symm

/-- 以 `k = n+1` 为自变量的缺口：`g(k) = 2π/k`。 -/
noncomputable def gapOf (k : ℕ) : ℝ := 2 * Real.pi / (k : ℝ)

/-- `gapOf (n+1)` 与 `gap n` 是同一个量（A 档）。 -/
theorem gapOf_succ (n : ℕ) : gapOf (n + 1) = gap n := by
  unfold gapOf gap
  push_cast
  ring

/-- **B.1 的精确形式**：`g_{ab-1} · 2π = g_{a-1} · g_{b-1}`（A 档）。
    证明只需 `ab` 的乘法性与 `2π/(ab) · 2π = (2π/a)(2π/b)`。 -/
theorem gap_mul (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    gap (a * b - 1) * (2 * Real.pi) = gap (a - 1) * gap (b - 1) := by
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  have hab : 1 ≤ a * b := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero ha0 hb0)
  have e1 : (((a * b - 1 : ℕ) : ℝ) + 1) = (a : ℝ) * (b : ℝ) := by
    rw [Nat.cast_sub hab]
    push_cast
    ring
  have e2 : (((a - 1 : ℕ) : ℝ) + 1) = (a : ℝ) := by
    rw [Nat.cast_sub ha]
    push_cast
    ring
  have e3 : (((b - 1 : ℕ) : ℝ) + 1) = (b : ℝ) := by
    rw [Nat.cast_sub hb]
    push_cast
    ring
  unfold gap
  rw [e1, e2, e3]
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha0
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb0
  have hp : (2 * Real.pi) ≠ 0 := by
    exact ne_of_gt (show (0 : ℝ) < 2 * Real.pi by positivity)
  field_simp

/-- 归一化缺口 `k ↦ 1/k`，取值落在尺度载体 `Scale` 上。 -/
noncomputable def gapUnit (k : ℕ) (hk : 0 < k) : Scale :=
  ⟨1 / (k : ℝ), one_div_pos.mpr (by exact_mod_cast hk)⟩

/-- **缺口是乘法同态**（A 档）：`k ↦ 1/k` 把 ({1,2,3,…}, ·) 送到乘法群 `Scale`。
    这是"尺度藏在缺口里"的正面证据：乘法律在 `k = n+1` 上精确成立。 -/
theorem gapUnit_mul (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    gapUnit (a * b)
        (Nat.mul_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one ha)
          (Nat.lt_of_lt_of_le Nat.zero_lt_one hb)) =
      gapUnit a (Nat.lt_of_lt_of_le Nat.zero_lt_one ha) *
        gapUnit b (Nat.lt_of_lt_of_le Nat.zero_lt_one hb) := by
  apply Scale.ext
  simp only [Scale.mul_val, gapUnit, one_div]
  push_cast
  rw [mul_inv_rev, mul_comm]

/-- **B.2**：`t ↦ 2π²/(2π−t)` 在 `{t_n}` 上的闭式是 `π(n+1)`（A 档）。 -/
theorem gapReversal_projectiveScale (n : ℕ) :
    2 * Real.pi ^ 2 / (2 * Real.pi - projectiveScale n) = Real.pi * ((n : ℝ) + 1) := by
  rw [← gap_eq_deficit n]
  unfold gap
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hp : (2 : ℝ) * Real.pi ≠ 0 := by
    exact ne_of_gt (show (0 : ℝ) < 2 * Real.pi by positivity)
  field_simp

/-- **该反演把时间坐标抛出 2π 之外**（A 档）：`π(n+1) ≥ 2π`（n ≥ 1）。 -/
theorem gapReversal_escapes (n : ℕ) (hn : 1 ≤ n) :
    2 * Real.pi ≤ Real.pi * ((n : ℝ) + 1) := by
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [Real.pi_pos]

/-- **B.2 的判定**：n ≥ 1 时，缺口反演的结果不再是任何 `t_m`（A 档，证否闭合性）。
    因为所有 `t_m < 2π`（`projectiveScale_lt_two_pi`），而反演结果 ≥ 2π。 -/
theorem gapReversal_out_of_range (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    2 * Real.pi ^ 2 / (2 * Real.pi - projectiveScale n) ≠ projectiveScale m := by
  intro h
  have h1 : 2 * Real.pi ≤ 2 * Real.pi ^ 2 / (2 * Real.pi - projectiveScale n) := by
    rw [gapReversal_projectiveScale]
    exact gapReversal_escapes n hn
  have h2 : projectiveScale m < 2 * Real.pi := projectiveScale_lt_two_pi m
  rw [h] at h1
  linarith

/-- **缺口反演没有实不动点**（A 档）：方程 `2π²/(2π−t) = t` 等价于
    `(t−π)² + π² = 0`，无实数解。故该反演不可能是连续对合。 -/
theorem gapReversal_no_fixed_point (t : ℝ) (ht : t ≠ 2 * Real.pi) :
    2 * Real.pi ^ 2 / (2 * Real.pi - t) ≠ t := by
  intro h
  have hd : 2 * Real.pi - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  rw [div_eq_iff hd] at h
  nlinarith [Real.pi_pos, sq_nonneg (t - Real.pi)]

/-- **B.4 的阴性见证**（A 档）：时间坐标 `t_n` 本身没有对应的乘法律。
    `gap_mul` 在 `g` 上成立（`g_0 = 2π`），但 `t_0 = 0`，于是取 `b = 1` 时
    乘积律退化为 `t_{a-1}·2π = 0`，对 `a = 2` 即为 `2π² = 0`，矛盾。
    故尺度结构只在缺口上，不在 `t_n` 上。 -/
theorem projectiveScale_not_mul :
    projectiveScale 1 * (2 * Real.pi) ≠ projectiveScale 1 * projectiveScale 0 := by
  have h0 : projectiveScale 0 = 0 := by
    unfold projectiveScale
    ring_nf
  have h1 : projectiveScale 1 = Real.pi := by
    unfold projectiveScale
    ring_nf
  rw [h0, h1]
  intro h
  nlinarith [Real.pi_pos]

end CSQIT.TimeScale
