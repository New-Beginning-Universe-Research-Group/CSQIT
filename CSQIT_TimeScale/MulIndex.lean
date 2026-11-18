/- ================================================================================
CSQIT — B 部分：乘法索引桥
文件: CSQIT_TimeScale/MulIndex.lean

上一轮的限定：`gapUnit` 是 ({1,2,3,…}, ·) → Scale 的精确乘法同态，但时间索引
`t_n` 只用了后继 `+1`，从不用乘法，所以"把索引换到乘法半群"缺一座桥。

本文件的判定：**桥不需要新公设**。关键观察是双射 `φ : ℕ ≃ {k // 0 < k}`（`n ↦ n+1`）
不是 (ℕ, ·) 到 (ℕ≥1, ·) 的同构——因为 `(a+1)(b+1) ≠ ab+1`。沿 φ 把
(ℕ≥1, ·) 的乘法拉回 ℕ，得到的是星号运算

    star a b = a * b + a + b        （因为 (a+1)(b+1) = star a b + 1）

(ℕ, star, 0) 是交换幺半群，且 φ 是 (ℕ, star, 0) ≃* (ℕ≥1, ·, 1) 的幺半群同构。
在这个索引上，缺口乘法律与时间坐标的换参闭式都精确成立：

    gap_star        : gap (star a b) * 2π = gap a * gap b
    time_under_star : t_{a∗b} = 2π − (g_a · g_b)/(2π)

序的结论（不粉饰）：换参后时间仍严格递增（`star_time_mono`、`star_strictMono_left`），
但乘法结构带来的是偏序（整除），不是全序；两者并存，序本身没有丢。

层级：A 档（零新增 axiom，零 sorry）
================================================================================ -/

import CSQIT_TimeScale.GapScale

namespace CSQIT.TimeScale

open CSQIT_W1.Foundation

/-- 沿 `n ↦ n+1` 把 (`ℕ`≥1, ·) 的乘法拉回 `ℕ` 得到的运算：`a ∗ b = ab + a + b`。 -/
def star (a b : ℕ) : ℕ := a * b + a + b

/-- `star` 以 0 为左幺元（A 档）。 -/
theorem star_zero_left (b : ℕ) : star 0 b = b := by
  unfold star
  omega

/-- `star` 以 0 为右幺元（A 档）。 -/
theorem star_zero_right (a : ℕ) : star a 0 = a := by
  unfold star
  omega

/-- `star` 交换（A 档）。 -/
theorem star_comm (a b : ℕ) : star a b = star b a := by
  unfold star
  ring

/-- `star` 结合（A 档）。 -/
theorem star_assoc (a b c : ℕ) : star (star a b) c = star a (star b c) := by
  unfold star
  ring

/-- **桥的核心恒等式**（A 档）：`star a b + 1 = (a+1)(b+1)`。
    这条把 ℕ 上的 `star` 与 ℕ≥1 上的乘法严格对齐。 -/
theorem star_succ_cast (a b : ℕ) :
    ((star a b : ℕ) : ℝ) + 1 = ((a : ℝ) + 1) * ((b : ℝ) + 1) := by
  unfold star
  push_cast
  ring

/-- **缺口乘法律在 ℕ 原生索引上的形式**（A 档）：
    `gap (a∗b) · 2π = gap a · gap b`。 -/
theorem gap_star (a b : ℕ) :
    gap (star a b) * (2 * Real.pi) = gap a * gap b := by
  unfold gap
  rw [star_succ_cast]
  have ha : (a : ℝ) + 1 ≠ 0 := by positivity
  have hb : (b : ℝ) + 1 ≠ 0 := by positivity
  have hp : (2 * Real.pi) ≠ 0 := ne_of_gt (show (0 : ℝ) < 2 * Real.pi by positivity)
  field_simp

/-- 缺口沿 `star` 的尺度值（A 档）。 -/
noncomputable def gapUnitAt (n : ℕ) : Scale :=
  ⟨1 / ((n : ℝ) + 1), one_div_pos.mpr (by positivity)⟩

/-- `gapUnitAt` 是 (ℕ, star) → Scale 的乘法同态（A 档）。 -/
theorem gapUnitAt_star (a b : ℕ) :
    gapUnitAt (star a b) = gapUnitAt a * gapUnitAt b := by
  apply Scale.ext
  simp only [Scale.mul_val, gapUnitAt, one_div]
  rw [star_succ_cast]
  rw [mul_inv_rev, mul_comm]

/-- **换参双射**（A 档）：`φ : ℕ → {k // 0 < k}`，`φ n = n+1`。
    时间索引换到乘法索引的合法性由这条保证。 -/
def phi : ℕ ≃ {k : ℕ // 0 < k} where
  toFun n := ⟨n + 1, Nat.succ_pos n⟩
  invFun k := k.1 - 1
  left_inv n := by simp
  right_inv k := by
    apply Subtype.ext
    exact Nat.sub_one_add_one (Nat.pos_iff_ne_zero.mp k.2)

/-- `φ` 的取值就是 `n+1`（A 档）。 -/
theorem phi_val (n : ℕ) : (phi n).1 = n + 1 := rfl

/-- **换参后的时间闭式**（A 档）：`t_{a∗b} = 2π − (g_a · g_b)/(2π)`。
    这是"乘法索引上的时间"的完整公式。 -/
theorem time_under_star (a b : ℕ) :
    projectiveScale (star a b) = 2 * Real.pi - gap a * gap b / (2 * Real.pi) := by
  have hp : (2 * Real.pi) ≠ 0 := ne_of_gt (show (0 : ℝ) < 2 * Real.pi by positivity)
  have h := gap_star a b
  have hg : gap (star a b) = gap a * gap b / (2 * Real.pi) := by
    rw [eq_div_iff hp]
    linarith
  have ht : projectiveScale (star a b) = 2 * Real.pi - gap (star a b) := by
    linarith [gap_eq_deficit (star a b)]
  rw [ht, hg]

/-- **序不丢**（A 档）：乘法索引不会让时间倒退，`t_a ≤ t_{a∗b}`。 -/
theorem star_time_mono (a b : ℕ) : projectiveScale a ≤ projectiveScale (star a b) := by
  apply projectiveScale_strictMono.monotone
  show a ≤ a * b + a + b
  calc a ≤ a + (a * b + b) := Nat.le_add_right a (a * b + b)
    _ = a * b + a + b := by ring

/-- **序不丢**（A 档）：固定 `b`，`a ↦ a∗b` 关于 `a` 严格递增。 -/
theorem star_strictMono_left (b : ℕ) : StrictMono (fun a : ℕ => star a b) := by
  intro a a' h
  unfold star
  have h1 : a * (b + 1) < a' * (b + 1) := Nat.mul_lt_mul_of_pos_right h (Nat.succ_pos b)
  have e1 : a * b + a = a * (b + 1) := by ring
  have e2 : a' * b + a' = a' * (b + 1) := by ring
  have h2 : a * b + a < a' * b + a' := by rw [e1, e2]; exact h1
  exact Nat.add_lt_add_right h2 b

end CSQIT.TimeScale
