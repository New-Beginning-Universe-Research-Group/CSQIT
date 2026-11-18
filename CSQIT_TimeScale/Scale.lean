/- ================================================================================
CSQIT — 「时间是尺度不是维度」：尺度一侧的最小形式化
文件: CSQIT_TimeScale/Scale.lean
定位: 独立目录，只读引用 CSQIT_W1 的既有声明，不改动任何既有文件

判定目标（Ju 提出的代数判据，本文件只落"尺度"这一半）：
  · 维度的代数结构 = 加法线序 (ℝ, +)，反演 t ↦ -t
  · 尺度的代数结构 = 乘法群 ℝ_{>0}，反演 t ↦ 1/t，取对数后才是加法

本文件把"尺度"做成真对象，并给出三条可判定的性质：
  1. 乘法交换律 / 结合律 / 逆元（`Scale.mul_comm'` 等）
  2. 反演 t ↦ 1/t 是乘法反自同构 `inv_mul'`，且严格反序 `inv_lt_inv_of_lt`
  3. 对数把乘法群同构为加法：`log_mul'`、`log_inv'`

层级：A 档（Mathlib 环境即可，零新增 axiom，零 sorry）
================================================================================ -/

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace CSQIT.TimeScale

/-- **尺度**：正实数的带证版本。与 `ℝ` 的区别只在 `pos` 字段——
    这个字段正是"乘法群"相对于"加法线"多出来的结构承诺。 -/
structure Scale where
  /-- 数值载体 -/
  val : ℝ
  /-- 尺度必须为正：没有零尺度，没有负尺度 -/
  pos : 0 < val

namespace Scale

/-- 两个尺度相等只需数值相等（`pos` 字段是命题，由证明无关性消去）。 -/
@[ext] theorem ext {s t : Scale} (h : s.val = t.val) : s = t := by
  cases s with
  | mk a ha =>
  cases t with
  | mk b hb =>
  simp only at h
  subst h
  rfl

noncomputable instance : One Scale := ⟨⟨1, one_pos⟩⟩

noncomputable instance : Mul Scale := ⟨fun s t => ⟨s.val * t.val, mul_pos s.pos t.pos⟩⟩

noncomputable instance : Inv Scale := ⟨fun s => ⟨s.val⁻¹, inv_pos.mpr s.pos⟩⟩

@[simp] theorem one_val : (1 : Scale).val = 1 := rfl

@[simp] theorem mul_val (s t : Scale) : (s * t).val = s.val * t.val := rfl

@[simp] theorem inv_val (s : Scale) : (s⁻¹).val = s.val⁻¹ := rfl

/-- 尺度乘法交换（A 档）。 -/
theorem mul_comm' (s t : Scale) : s * t = t * s := by
  ext
  simp only [mul_val]
  exact mul_comm s.val t.val

/-- 尺度乘法结合（A 档）。 -/
theorem mul_assoc' (s t u : Scale) : s * t * u = s * (t * u) := by
  ext
  simp only [mul_val]
  exact mul_assoc s.val t.val u.val

/-- 单位律（A 档）。 -/
theorem one_mul' (s : Scale) : 1 * s = s := by
  ext
  simp

/-- 单位律（A 档）。 -/
theorem mul_one' (s : Scale) : s * 1 = s := by
  ext
  simp

/-- 反演是对合：`t ↦ 1/t` 两次回到自身（A 档）。
    维度式反演 `t ↦ -t` 同样是对合，但固定点不同（0 对 1）。 -/
theorem inv_inv' (s : Scale) : s⁻¹⁻¹ = s := by
  ext
  simp

/-- 逆元律（A 档）。 -/
theorem mul_inv_cancel' (s : Scale) : s * s⁻¹ = 1 := by
  ext
  simp only [mul_val, inv_val, one_val]
  exact mul_inv_cancel₀ (ne_of_gt s.pos)

/-- **反演是乘法反自同构**：`(st)⁻¹ = s⁻¹ t⁻¹`（A 档）。
    这是尺度式反演与维度式反演的分水岭：`t ↦ -t` 对加法是同态，
    对乘法不是；`t ↦ 1/t` 对乘法是同态，对加法不是。 -/
theorem inv_mul' (s t : Scale) : (s * t)⁻¹ = s⁻¹ * t⁻¹ := by
  ext
  simp only [mul_val, inv_val]
  rw [mul_inv_rev, mul_comm]

/-- 反演的固定点：1（A 档）。`t ↦ -t` 的固定点是 0，这一条把两者分开。 -/
theorem inv_one' : (1 : Scale)⁻¹ = 1 := by
  ext
  simp

/-- **反演严格反序**（A 档）：`s < t → t⁻¹ < s⁻¹`。 -/
theorem inv_lt_inv_of_lt {s t : Scale} (h : s.val < t.val) : (t⁻¹).val < (s⁻¹).val := by
  simp only [inv_val]
  have h' : 1 / t.val < 1 / s.val := one_div_lt_one_div_of_lt s.pos h
  simpa [one_div] using h'

/-- **对数把乘法群同构为加法**（A 档）：
    `log (s·t) = log s + log t`。这是"尺度取对数才是维度"的形式陈述，
    但它作用在 `Scale` 上，不作用在时间坐标上。 -/
theorem log_mul' (s t : Scale) :
    Real.log (s * t).val = Real.log s.val + Real.log t.val := by
  simp only [mul_val]
  exact Real.log_mul (ne_of_gt s.pos) (ne_of_gt t.pos)

/-- **对数把反演变成取负**（A 档）：`log (s⁻¹) = - log s`。
    即：尺度反演 `1/t` 在对数坐标下退化为维度反演 `-x`。 -/
theorem log_inv' (s : Scale) : Real.log (s⁻¹).val = -Real.log s.val := by
  simp only [inv_val]
  exact Real.log_inv s.val

/-- 对数单位律（A 档）。 -/
theorem log_one' : Real.log (1 : Scale).val = 0 := by
  simp [one_val]

end Scale

end CSQIT.TimeScale
