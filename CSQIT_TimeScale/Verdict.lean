/- ================================================================================
CSQIT — 判定：既有体系里的时间是"有序坐标"，不是尺度
文件: CSQIT_TimeScale/Verdict.lean

本文件只读引用 CSQIT_W1 的既定声明（Foundation / AlgebraicTimeCircle /
QuantumTimeCircle），不改动其任何陈述与证明。给出四条可判定的判定结论：

  1. `projectiveScale_injective` / `projectiveScale_aperiodic`
     时间坐标在 ℕ 上单射，因此不存在 420 周期——"周期 420" 只住在
     `TimeCircleWeave.period : ℕ` 这个字段里，不在坐标里。
  2. `period_is_a_field_not_a_coordinate`
     把上面这条与 `ourUniverse_period_eq_totalClosure` 并列：字段相等，坐标不周期。
  3. `deficit_eq`
     `2π - projectiveScale n = 2π/(n+1)`：乘法式（倒数）只出现在"到 2π 的缺口"里，
     不出现在时间坐标本身。
  4. `existing_reversal_is_negation`
     既有的"时间反演"在真圆 S¹ 上就是加法取负 `θ ↦ -θ`，即维度式反演，
     不是尺度式反演 `θ ↦ 1/θ`。配合 `timeCircleUnified_conjecture_false`，
     说明 `QuantumTimeCircle.time_circle_unified_conjecture` 为假。

层级：A 档（零新增 axiom，零 sorry）
================================================================================ -/

import CSQIT_W1.QuantumTimeCircle
import CSQIT_TimeScale.Spiral

namespace CSQIT.TimeScale

open CSQIT_W1.Foundation

/-- 时间坐标 `2πn/(n+1)` 在 ℕ 上单射（A 档，继承 `projectiveScale_strictMono`）。 -/
theorem projectiveScale_injective : Function.Injective projectiveScale :=
  projectiveScale_strictMono.injective

/-- **时间坐标没有 420 周期**（A 档）：对任意 n，前进 420 步后相位不同。 -/
theorem projectiveScale_aperiodic (n : ℕ) :
    projectiveScale (n + 420) ≠ projectiveScale n := by
  intro h
  have hlt : n < n + 420 := Nat.lt_add_of_pos_right (by norm_num)
  exact (projectiveScale_strictMono hlt).ne h.symm

/-- **周期是字段，不是坐标**（A 档）：
    `OurUniverse.period` 等于 420，而时间坐标上不存在 420 周期。 -/
theorem period_is_a_field_not_a_coordinate :
    CSQIT.V12.AlgebraicTimeCircle.OurUniverse.period = 420 ∧
      ∀ n : ℕ, projectiveScale (n + 420) ≠ projectiveScale n := by
  constructor
  · rw [CSQIT.V12.AlgebraicTimeCircle.ourUniverse_period_eq_totalClosure,
      totalClosure_eq_420]
  · exact projectiveScale_aperiodic

/-- **缺口定理**（A 档）：`2π - 2πn/(n+1) = 2π/(n+1)`。
    乘法式的倒数结构只出现在到 2π 的缺口上；时间坐标本身只被序使用。 -/
theorem deficit_eq (n : ℕ) :
    2 * Real.pi - projectiveScale n = 2 * Real.pi / ((n : ℝ) + 1) := by
  unfold projectiveScale
  have h : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- **既有"时间反演"在真圆上就是加法取负**（A 档）：
    `2π - θ` 与 `-θ` 是 `AddCircle (2π)` 上的同一点。
    即：既有实现是维度式反演 `t ↦ -t`，不是尺度式反演 `t ↦ 1/t`。 -/
theorem existing_reversal_is_negation (θ : ℝ) :
    ((2 * Real.pi - θ : ℝ) : Phase) = -(θ : Phase) := by
  have h : 2 * Real.pi - θ = -θ + 2 * Real.pi := by ring
  rw [h, AddCircle.coe_add_period, AddCircle.coe_neg]

/-- **`time_circle_unified_conjecture` 为假**（A 档）。
    该猜想断言 `closure_to_unitary_circle (n+420) = closure_to_unitary_circle n`，
    与 `projectiveScale_aperiodic` 直接冲突。 -/
theorem timeCircleUnified_conjecture_false :
    ¬ CSQIT.V12.QuantumTimeCircle.time_circle_unified_conjecture := by
  intro h
  refine projectiveScale_aperiodic 0 ?_
  simpa [CSQIT.V12.QuantumTimeCircle.closure_to_unitary_circle] using h 0

end CSQIT.TimeScale
