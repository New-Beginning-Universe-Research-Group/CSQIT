/- ================================================================================
CSQIT — 螺旋：S¹ × ℝ_{>0}
文件: CSQIT_TimeScale/Spiral.lean

载体选择与理由：
  · 第一因子用 `AddCircle (2π)`（Mathlib 的真商圆），而不是既有
    `AlgebraicTimeCircle.TimeCircle`（`{θ : ℝ // 0 ≤ θ ∧ θ < 2π}` 的区间子类型）。
    原因：区间子类型上 0 与 2π 没有被等同，加不出群结构；它是"圆的坐标系"，
    不是圆。换成 `AddCircle` 是**环境问题**（Mathlib 已有），不是新公设。
  · 第二因子用 `Scale`（见 Scale.lean），即 ℝ_{>0}。

落地的三条内容：
  1. `Spiral` 是一个真的乘法对象：`projScale_mul` 说明投影到尺度因子是乘性的
  2. `phase_add_period` / `spiralOfPhase_period`：相位因子周期恰为 2π
  3. `scaleAt_add` / `scaleAt_log_add`：由索引 n 提升的尺度 2^n 是乘性的，
     且取对数后变成加法——"上升"就是这一维的单调性

层级：A 档（零新增 axiom，零 sorry）
================================================================================ -/

import Mathlib.Topology.Instances.AddCircle.Defs
import CSQIT_TimeScale.Scale
import CSQIT_W1.Foundation

namespace CSQIT.TimeScale

open CSQIT_W1.Foundation

/-- **相位圆**：真商圆 ℝ / 2πℤ，继承 `AddCommGroup` 与拓扑。 -/
abbrev Phase : Type := AddCircle (2 * Real.pi)

/-- **螺旋**：相位因子 × 尺度因子。
    投影 `projPhase` 给"周期"，投影 `projScale` 给"单调尺度"，
    两者合起来就是"螺旋上升"的对象化。 -/
structure Spiral where
  /-- 相位因子（圆） -/
  phase : Phase
  /-- 尺度因子（乘法群） -/
  scale : Scale

namespace Spiral

@[ext] theorem ext {u v : Spiral} (hp : u.phase = v.phase) (hs : u.scale = v.scale) : u = v := by
  cases u with
  | mk p s =>
  cases v with
  | mk q t =>
  simp only at hp hs
  subst hp
  subst hs
  rfl

/-- 螺旋的乘法：相位相加、尺度相乘。 -/
noncomputable instance : Mul Spiral := ⟨fun u v => ⟨u.phase + v.phase, u.scale * v.scale⟩⟩

noncomputable instance : One Spiral := ⟨⟨0, 1⟩⟩

noncomputable instance : Inv Spiral := ⟨fun u => ⟨-u.phase, u.scale⁻¹⟩⟩

@[simp] theorem mul_phase (u v : Spiral) : (u * v).phase = u.phase + v.phase := rfl

@[simp] theorem mul_scale (u v : Spiral) : (u * v).scale = u.scale * v.scale := rfl

theorem mul_comm' (u v : Spiral) : u * v = v * u := by
  apply Spiral.ext
  · simp only [mul_phase]
    exact add_comm u.phase v.phase
  · exact Scale.mul_comm' u.scale v.scale

theorem inv_inv' (u : Spiral) : u⁻¹⁻¹ = u := by
  apply Spiral.ext
  · show -(-u.phase) = u.phase
    exact neg_neg u.phase
  · show (u.scale⁻¹)⁻¹ = u.scale
    exact Scale.inv_inv' u.scale

/-- 投影到尺度因子。 -/
def projScale (u : Spiral) : Scale := u.scale

/-- 投影到相位因子。 -/
def projPhase (u : Spiral) : Phase := u.phase

/-- **投影到尺度因子是乘性的**（A 档）：`proj (u·v) = proj u · proj v`。 -/
theorem projScale_mul (u v : Spiral) :
    projScale (u * v) = projScale u * projScale v := rfl

/-- 投影到相位因子是加性的（A 档）：`proj (u·v) = proj u + proj v`。 -/
theorem projPhase_mul (u v : Spiral) :
    projPhase (u * v) = projPhase u + projPhase v := rfl

/-- **相位因子周期为 2π**（A 档）：`θ + 2π` 与 `θ` 是圆上同一点。
    用的是 Mathlib 的 `AddCircle.coe_add_period`，不是定义出来的"周期"。 -/
theorem phase_add_period (θ : ℝ) : ((θ + 2 * Real.pi : ℝ) : Phase) = (θ : Phase) :=
  AddCircle.coe_add_period (p := 2 * Real.pi) θ

/-- 由实数角构造螺旋点。 -/
noncomputable def spiralOfPhase (θ : ℝ) (s : Scale) : Spiral := ⟨(θ : Phase), s⟩

/-- **螺旋的相位部分周期为 2π**（A 档）。 -/
theorem spiralOfPhase_period (θ : ℝ) (s : Scale) :
    spiralOfPhase (θ + 2 * Real.pi) s = spiralOfPhase θ s := by
  unfold spiralOfPhase
  rw [phase_add_period]

/-- 由闭包索引提升的尺度因子：`2ⁿ`。
    选 `2ⁿ` 而不是 `n+1` 的理由：它满足乘法律 `2^(m+n) = 2^m·2^n`，
    而 `n+1` 不满足——"尺度"这个词只有在乘法律成立时才有代数内容。 -/
noncomputable def scaleAt (n : ℕ) : Scale := ⟨(2 : ℝ) ^ n, pow_pos (by norm_num) n⟩

/-- **尺度因子对索引是乘性的**（A 档）。 -/
theorem scaleAt_add (m n : ℕ) :
    (scaleAt (m + n)).val = (scaleAt m).val * (scaleAt n).val := by
  show (2 : ℝ) ^ (m + n) = (2 : ℝ) ^ m * (2 : ℝ) ^ n
  exact pow_add 2 m n

/-- **尺度因子的对数是加性的**（A 档）：`log 2^(m+n) = log 2^m + log 2^n`。 -/
theorem scaleAt_log_add (m n : ℕ) :
    Real.log (scaleAt (m + n)).val =
      Real.log (scaleAt m).val + Real.log (scaleAt n).val := by
  rw [scaleAt_add m n]
  exact Scale.log_mul' (scaleAt m) (scaleAt n)

/-- **尺度因子严格单调递增**（A 档）：这就是"上升"。 -/
theorem scaleAt_strictMono : StrictMono (fun n : ℕ => (scaleAt n).val) := by
  intro m n h
  show (2 : ℝ) ^ m < (2 : ℝ) ^ n
  have h2 : (2 : ℕ) ^ m < (2 : ℕ) ^ n := Nat.pow_lt_pow_right (by norm_num) h
  exact_mod_cast h2

/-- 索引 → 螺旋点：相位取既有 `projectiveScale`，尺度取 `2ⁿ`。 -/
noncomputable def spiralAt (n : ℕ) : Spiral :=
  ⟨(projectiveScale n : Phase), scaleAt n⟩

/-- **螺旋上升**（A 档）：沿索引前进时，尺度因子按乘法增长。 -/
theorem spiralAt_scale_mul (m n : ℕ) :
    (spiralAt (m + n)).scale.val =
      (spiralAt m).scale.val * (spiralAt n).scale.val :=
  scaleAt_add m n

end Spiral

end CSQIT.TimeScale
