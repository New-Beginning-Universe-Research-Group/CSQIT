/-
Copyright (c) 2026 CSQIT. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.Real.Irrational
import CSQIT_W1.Foundation
import CSQIT_V1Bridge.FreeModel

/-!
# 层级切口的可编译骨架

本模块只落地三个切口里**已经能证**的部分，不引入任何新公设：

1. **切口 1：能隙零点集。** 取**加权路径图**上的 Laplacian 二次型
   `pathLapForm w f = ∑ i, w i * (f (i+1) - f i)^2`。证明：
   (a) 二次型非负；
   (b) 正权下，二次型为零 ⇔ 相邻差全为零 ⇔ `f` 为常函数；
   (c) 零点集与正权重的具体取值无关。
   这说明「零点集」是**结构对象**，不是数值谱隙。注意：这里形式化的是零点集，
   不是最小非零特征值；后者 Mathlib 的 `SimpleGraph.LapMatrix` 也未提供。

   为什么不用 `SimpleGraph.LapMatrix`：它的 `Analysis.Matrix.Order` 依赖闭包在本
   `.lake` 中只建成了 182/788 个 `Analysis` 文件，直接导入会触发数小时的 Mathlib
   重编译。路径图版本是同一个零点集命题的一维实现，证明强度为 B 档；一般图的
   A 档版本在 Mathlib 中已有（`lapMatrix_mulVec_eq_zero_iff_forall_reachable`、
   `card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`），本轮不导入。

2. **切口 4：压缩比。** 对有限维线性粗粒化算符 `P : E →ₗ[ℝ] E`，定义
   `compressionRatio P = finrank (range P) / finrank E`。证明它与零度互补
   （秩–零度定理）、非平凡核等价于 `r < 1`。对规则层给出否定式桥：
   非单射 `π` 不可能因子化一个单射振幅。

3. **切口 5：跑动耦合不是层不变量。** 在见证模型上，任意同态 `φ` 的振幅沿流
   恰为 `amp(φ 0)^(n+1)`；因此振幅沿流恒常 **当且仅当** `amp(φ 0) = 1`。
   结合 `amplitude_ne_zero`，任何非 1 的初值都在跑动。α 一类量不是层间不变量。

## 纪律

- 零新增 `axiom`，零 `sorry` / `admit`。
- 不改动 `CSQIT_W1`、`CSQIT_Enhanced` 的任何既有声明。
- 所有新假设均以结构字段（`AxiomA`/`AxiomC`）或定理前提显式出现。

## 理论边界（与代码一一对应）

- `pathLapForm` 是**定义**，不是「层界」的物理断言；把层界等同于零点集属于诠释
  （C 档）。
- `compressionRatio` 是**定义**；产生「层间距离」需要额外指定一族随尺度参数化的
  `P_s`，本模块不提供该族。
- `flowAmplitude_layerInvariant_iff` 是 A 档否定式定理，只说明振幅随流跑动，
  不说明跑动量的数值；数值仍是外部输入（与 `no_determiner` 一致）。
-/

namespace CSQIT_LayerCuts

open CSQIT_W1.Foundation
open CSQIT_V1Bridge

/-! ============================================================================
    §1. 切口 1：能隙零点集（加权路径图的 Laplacian 二次型）
   ============================================================================ -/

section PathZeroModes

/-- **定义（零点集）**：加权路径图 `0—1—…—n` 上的 Laplacian 二次型。

    `f : Fin (n+1) → ℝ` 是顶点函数，`w : Fin n → ℝ` 是边权。
    这是「能隙零点集」的一维可形式化替身：`pathLapForm w f = 0` 的解空间。
    它不是数值谱隙，而是零模集合。 -/
def pathLapForm {n : ℕ} (w : Fin n → ℝ) (f : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin n, w i * (f i.succ - f i.castSucc) ^ 2

/-- **B 档**：正权下二次型非负。 -/
theorem pathLapForm_nonneg {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i)
    (f : Fin (n + 1) → ℝ) : 0 ≤ pathLapForm w f := by
  unfold pathLapForm
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)

/-- **B 档（局部零点刻画）**：正权下二次型为零 ⇔ 每条边两端取值相同。

    证明只用「非负数之和为零 ⇔ 每项为零」与整环消去，不需要谱理论。 -/
theorem pathLapForm_eq_zero_iff {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, 0 < w i)
    {f : Fin (n + 1) → ℝ} :
    pathLapForm w f = 0 ↔ ∀ i : Fin n, f i.succ = f i.castSucc := by
  constructor
  · intro h
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ w i * (f i.succ - f i.castSucc) ^ 2 := by
      intro i _
      exact mul_nonneg (le_of_lt (hw i)) (sq_nonneg _)
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h
    intro i
    have hi : w i * (f i.succ - f i.castSucc) ^ 2 = 0 := hzero i (Finset.mem_univ i)
    have hsq : (f i.succ - f i.castSucc) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hi with hw0 | hsq
      · exact absurd hw0 (ne_of_gt (hw i))
      · exact hsq
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · intro h
    unfold pathLapForm
    exact Finset.sum_eq_zero fun i _ => by simp [h i]

/-- **B 档（全局常数化）**：相邻差全为零 ⇒ 顶点函数为常函数（路径连通）。 -/
theorem path_const_of_adj_eq {n : ℕ} {f : Fin (n + 1) → ℝ}
    (h : ∀ i : Fin n, f i.succ = f i.castSucc) :
    ∀ i : Fin (n + 1), f i = f 0 := by
  intro i
  induction i using Fin.induction with
  | zero => rfl
  | succ j ih => exact (h j).trans ih

/-- **B 档（零点集 = 常函数）**：正权路径图的零模恰为常函数。 -/
theorem pathLapForm_eq_zero_iff_const {n : ℕ} {w : Fin n → ℝ} (hw : ∀ i, 0 < w i)
    {f : Fin (n + 1) → ℝ} :
    pathLapForm w f = 0 ↔ ∀ i j : Fin (n + 1), f i = f j := by
  rw [pathLapForm_eq_zero_iff hw]
  constructor
  · intro h i j
    exact (path_const_of_adj_eq h i).trans (path_const_of_adj_eq h j).symm
  · intro h i
    exact h i.succ i.castSucc

/-- **B 档（细节无关性）**：零点集与正权重的具体取值无关。

    只要所有权为正，零模集合都恰为常函数；边权的大小、比例、几何全不进入。 -/
theorem pathZeroMode_indep_of_pos_weights {n : ℕ} {w w' : Fin n → ℝ}
    (hw : ∀ i, 0 < w i) (hw' : ∀ i, 0 < w' i) {f : Fin (n + 1) → ℝ} :
    pathLapForm w f = 0 ↔ pathLapForm w' f = 0 := by
  rw [pathLapForm_eq_zero_iff_const hw, pathLapForm_eq_zero_iff_const hw']

end PathZeroModes

/-! ============================================================================
   §2. 切口 4：压缩比 d_eff / D
   ============================================================================ -/

section CompressionRatio

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- **定义（有效维度）**：粗粒化算符像的维数。 -/
noncomputable def effectiveDim (P : E →ₗ[ℝ] E) : ℕ :=
  Module.finrank ℝ (LinearMap.range P)

/-- **定义（压缩比）**：`d_eff / D`，取值在 `[0,1]` 的层间距离补数。 -/
noncomputable def compressionRatio (P : E →ₗ[ℝ] E) : ℚ :=
  (effectiveDim P : ℚ) / (Module.finrank ℝ E : ℚ)

/-- `D` 作为正有理数非零（`E` 非平凡）。 -/
theorem finrank_ne_zero_rat : (Module.finrank ℝ E : ℚ) ≠ 0 := by
  have hpos : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hposq : (0 : ℚ) < (Module.finrank ℝ E : ℚ) := by exact_mod_cast hpos
  exact hposq.ne'

/-- **B 档（秩–零度）**：压缩比与相对零度互补。

    `r + dim ker P / D = 1`。这是「信息损失」的精确记账。 -/
theorem compressionRatio_add_nullity (P : E →ₗ[ℝ] E) :
    compressionRatio P + (Module.finrank ℝ (LinearMap.ker P) : ℚ) /
        (Module.finrank ℝ E : ℚ) = 1 := by
  have hD := finrank_ne_zero_rat (E := E)
  have h := P.finrank_range_add_finrank_ker
  have hq : (effectiveDim P : ℚ) + (Module.finrank ℝ (LinearMap.ker P) : ℚ) =
      (Module.finrank ℝ E : ℚ) := by
    unfold effectiveDim
    exact_mod_cast h
  rw [compressionRatio, div_eq_mul_inv, div_eq_mul_inv, ← add_mul, hq]
  exact mul_inv_cancel₀ hD

/-- **B 档**：压缩比不超过 1。 -/
theorem compressionRatio_le_one (P : E →ₗ[ℝ] E) : compressionRatio P ≤ 1 := by
  have hD : (0 : ℚ) < (Module.finrank ℝ E : ℚ) := by
    have hpos : 0 < Module.finrank ℝ E := Module.finrank_pos
    exact_mod_cast hpos
  rw [compressionRatio, div_le_one hD]
  unfold effectiveDim
  exact_mod_cast (LinearMap.range P).finrank_le

/-- **B 档**：核为零（无损压缩）⇒ 压缩比为 1。 -/
theorem compressionRatio_eq_one_of_ker_eq_bot (P : E →ₗ[ℝ] E)
    (h : LinearMap.ker P = ⊥) : compressionRatio P = 1 := by
  have hD := finrank_ne_zero_rat (E := E)
  have hk : Module.finrank ℝ (LinearMap.ker P) = 0 := by simp [h]
  have hsum := P.finrank_range_add_finrank_ker
  have hEq : Module.finrank ℝ (LinearMap.range P) = Module.finrank ℝ E := by omega
  rw [compressionRatio]
  unfold effectiveDim
  rw [hEq]
  exact div_self hD

/-- **B 档**：核非平凡（真降维）⇒ 压缩比严格小于 1。 -/
theorem compressionRatio_lt_one_of_ker_ne_bot (P : E →ₗ[ℝ] E)
    (h : LinearMap.ker P ≠ ⊥) : compressionRatio P < 1 := by
  have hD : (0 : ℚ) < (Module.finrank ℝ E : ℚ) := by
    have hpos : 0 < Module.finrank ℝ E := Module.finrank_pos
    exact_mod_cast hpos
  have hk : 1 ≤ Module.finrank ℝ (LinearMap.ker P) :=
    Submodule.one_le_finrank_iff.mpr h
  have hsum := P.finrank_range_add_finrank_ker
  have hlt : Module.finrank ℝ (LinearMap.range P) < Module.finrank ℝ E := by omega
  rw [compressionRatio, div_lt_one hD]
  unfold effectiveDim
  exact_mod_cast hlt

end CompressionRatio

/-! ============================================================================
   §2b. 切口 4 的规则层桥：真降维必然重标定振幅
   ============================================================================ -/

section RuleLevelCoarseGraining

variable {M C C' : Type*} [A : AxiomA M C] [Cx : AxiomC M C]

/-- **A 档（纯因子化引理）**：单射振幅被 `π` 因子化 ⇒ `π` 单射。

    不需要目标侧 `AxiomC`；只用到源振幅单射。 -/
theorem amplitude_factorization_injective {amp : C → ℂ} (hinj : Function.Injective amp)
    (π : C → C') (amp' : C' → ℂ) (h : ∀ α : C, amp' (π α) = amp α) :
    Function.Injective π := by
  intro a b hab
  apply hinj
  rw [← h a, ← h b, hab]

/-- **A 档（否定式桥）**：若 `π` 把两个规则合并（非单射），则不存在任何目标振幅
    `amp'` 使它守恒源振幅。

    这就是「真正的粗粒化必然改变振幅标签」的精确形式；与 G36a 同一机制，
    但不需要目标侧 `AxiomC`，因此可直接用于「降维 ⇒ 跑动」的论证。 -/
theorem no_amplitude_factorization_of_not_injective (π : C → C')
    (hnot : ¬ Function.Injective π) :
    ¬ ∃ amp' : C' → ℂ, ∀ α : C, amp' (π α) = Cx.amplitude α := by
  rintro ⟨amp', h⟩
  exact hnot (amplitude_factorization_injective Cx.amplitude_injective π amp' h)

end RuleLevelCoarseGraining

/-! ============================================================================
   §3. 切口 5：跑动耦合 / α 不是层间不变量
   ============================================================================ -/

section FlowAmplitude

variable {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]

/-- **定义（层不变量）**：沿流恒常的量。 -/
def LayerInvariant (f : ℕ → ℂ) : Prop := ∀ n, f n = f 0

/-- 见证模型同态的振幅是几何序列 `amp(φ 0)^(n+1)`；这是 G24/G42e 的直接读法。 -/
theorem flow_amplitude_pow (φ : ℕ → C)
    (hφ : ∀ a b : ℕ, φ (a + b + 1) = A.compose (φ a) (φ b)) (n : ℕ) :
    Cx.amplitude (φ n) = (Cx.amplitude (φ 0)) ^ (n + 1) :=
  witnessHom_amplitude (A := A) (Cx := Cx) φ hφ n

/-- **A 档**：振幅沿流是层不变量 **当且仅当** 初值为 1。

    证明只用 `amp(φ 1) = amp(φ 0)^2`、`amp ≠ 0` 与整环消去。
    这直接回答「α 是不是层间不变量」：任何非 1 的耦合都在跑动。 -/
theorem flowAmplitude_layerInvariant_iff (φ : ℕ → C)
    (hφ : ∀ a b : ℕ, φ (a + b + 1) = A.compose (φ a) (φ b)) :
    LayerInvariant (fun n => Cx.amplitude (φ n)) ↔ Cx.amplitude (φ 0) = 1 := by
  constructor
  · intro h
    have hpow : Cx.amplitude (φ 1) = (Cx.amplitude (φ 0)) ^ 2 := by
      simpa using flow_amplitude_pow (A := A) (Cx := Cx) φ hφ 1
    have hc2 : (Cx.amplitude (φ 0)) ^ 2 = Cx.amplitude (φ 0) := by
      rw [← hpow]
      exact h 1
    have hfac : Cx.amplitude (φ 0) * (Cx.amplitude (φ 0) - 1) = 0 := by
      have hsub : (Cx.amplitude (φ 0)) ^ 2 - Cx.amplitude (φ 0) = 0 := by
        rw [hc2, sub_self]
      calc Cx.amplitude (φ 0) * (Cx.amplitude (φ 0) - 1)
          = (Cx.amplitude (φ 0)) ^ 2 - Cx.amplitude (φ 0) := by ring
        _ = 0 := hsub
    rcases mul_eq_zero.mp hfac with h0 | h1
    · exact absurd h0 (amplitude_ne_zero (φ 0))
    · exact sub_eq_zero.mp h1
  · intro hc n
    simp [flow_amplitude_pow (A := A) (Cx := Cx) φ hφ n, hc]

/-- **A 档（否定式）**：初值非 1 的流，其振幅不是层不变量。 -/
theorem flowAmplitude_not_layerInvariant (φ : ℕ → C)
    (hφ : ∀ a b : ℕ, φ (a + b + 1) = A.compose (φ a) (φ b))
    (h1 : Cx.amplitude (φ 0) ≠ 1) :
    ¬ LayerInvariant (fun n => Cx.amplitude (φ n)) := fun h =>
  h1 ((flowAmplitude_layerInvariant_iff (A := A) (Cx := Cx) φ hφ).mp h)

/-- **A 档（平凡性）**：任何规则的振幅模长恒为 1，因此由模长构造的「不变量」
    只能是常数 1；α 一类量不可能从 `AxiomC` 的模长直接读出。 -/
theorem amplitude_normSq_eq_one (α : C) : Complex.normSq (Cx.amplitude α) = 1 :=
  Cx.norm_one α

end FlowAmplitude

end CSQIT_LayerCuts
