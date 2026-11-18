/- ================================================================================
CSQIT — A 部分：1、2、3 次幂的来源
文件: CSQIT_TimeScale/PowerLaw.lean

库中 `1/(n+1)` 的幂次共三处（另有一处维度式的补 `n/(n+1)`）：
  · speedOfLight      = 2π/(n+1)²        Foundation.lean:310-311
  · planckMass       ∝ 1/(n+1)           Foundation.lean:1104-1107
  · weave_curvature  = 4π/(n+1)³         GravitationalAnomaly.lean:33-34

幂次在 def 体里都是**字面数字**（A.2 分类为 (a)），但本文件证明它们不是三个
互不相关的指数，而是同一个量——缺口 `g_n = 2π/(n+1)`——的三次幂：

    speedOfLight      n = g_n² / (2π)
    weave_curvature   n = g_n³ / (2π²)
    planckMass        n = W · sqrt(2π·420^5) · g_n / (2π)

即幂次 1、2、3 是 `g_n` 的幂，而不是某个"结构维数"字段的读数：全库
`grep 'dimension|massDim|dim :'` 零命中（详见收尾报告），故"幂次 = 维数"
这一假说在现有代码中**无法检验**。

层级：A 档（零新增 axiom，零 sorry）
================================================================================ -/

import CSQIT_TimeScale.GapScale
import CSQIT_W1.GravitationalAnomaly

namespace CSQIT.TimeScale

open CSQIT_W1.Foundation
open CSQIT_W1.Foundation.PlanckMassDerivation
open CSQIT.V12.GravitationalAnomaly

/-- 光速的 2 次幂就是缺口的 2 次幂（差常数 `1/(2π)`）（A 档）。 -/
theorem speedOfLight_eq_gap_sq (n : ℕ) :
    speedOfLight n = gap n ^ 2 / (2 * Real.pi) := by
  unfold speedOfLight gap
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hp : (2 * Real.pi) ≠ 0 := ne_of_gt (show (0 : ℝ) < 2 * Real.pi by positivity)
  field_simp <;> ring_nf

/-- 编织曲率的 3 次幂就是缺口的 3 次幂（差常数 `1/(2π²)`）（A 档）。 -/
theorem weave_curvature_eq_gap_cu (n : ℕ) :
    weave_curvature n = gap n ^ 3 / (2 * Real.pi ^ 2) := by
  unfold weave_curvature gap
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hp : (2 * Real.pi) ≠ 0 := ne_of_gt (show (0 : ℝ) < 2 * Real.pi by positivity)
  field_simp <;> ring_nf

/-- 普朗克质量的 1 次幂就是缺口的 1 次幂（差常数因子）（A 档）。 -/
theorem planckMass_eq_gap (n : ℕ) :
    planckMass n =
      CSQIT_W1.Foundation.PlanckMassDerivation.weavingStiffnessBase *
        Real.sqrt (timeCircleCircumference * (totalClosure : ℝ) ^ spinNetworkExponent) *
        gap n / (2 * Real.pi) := by
  unfold planckMass gap
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hp : (2 * Real.pi) ≠ 0 := ne_of_gt (show (0 : ℝ) < 2 * Real.pi by positivity)
  field_simp <;> ring_nf

end CSQIT.TimeScale
