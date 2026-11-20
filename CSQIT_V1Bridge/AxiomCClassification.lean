/-
================================================================================
CSQIT_V1Bridge — 见证 compose 上 AxiomC 的完全分类（G24）
模块: CSQIT_V1Bridge.AxiomCClassification
版本: v0.1.0（2026-11-07）
================================================================================

承接 `BOUNDARIES.md` §15（停在 G23）。G20 已证「同一 compose 上存在两个
AxiomC」，但那只是存在性：S 与 compose 之间的全部自由度是多少？本模块
在见证模型 `(ℕ, a+b+1)` 上给出**完全分类**：

  §1 递归展开：任何满足 `compose a b = a+b+1` 的 `AxiomA` 上的 `AxiomC`，
     必有 `amplitude n = amplitude 0 ^ (n+1)`（乘法性 + 归纳）。
     即：**一个点（0 处振幅 c）决定整个振幅层**。
  §2 构造方向：任何 `|c| = 1` 且非单位根的 `c` 反向给出合法 `AxiomC`
     （`powAxiomC`），单射性 ⟺ `c` 非单位根。
  §3 相等判据：两个 `AxiomC` 相等 ⟺ 它们在 0 处的振幅相等。
     振幅层数据无冗余：恰为一个圆上非单位根参数。
  §4 作用量参数化：`S(n) = (n+1) • S(0)`——作用量是生成元相位的
     整数倍；规范自由度恰为 `S(0)` 一个角度。
  §5 见证实例化：`witnessAmplitude 0 = exp(iπ√2)` 非单位根；
     分类定理回填 witness/alt 两个实例，G20 成为分类的两个成员。

结构含义（回答用户重点问题 #2 的「振幅层是什么」）：
  在 v23 的唯一非空通道（见证 compose）上，V1 的振幅层不是含丰富
  物理结构的层，而是**一个 U(1) 参数的重复扫描**：c ∈ 圆∖单位根。
  它的全部信息 = 单点相位；它的全部动力学 = 该相位的整数倍。
  这不是否定（G20 已做），而是**刻画的完成**：说明振幅层再无
  其他自由度可挖。

边界（不夸大）：
  分类只在 `compose a b = a+b+1` 的模型上成立；v23 的一般模型
  （左投影、加法等）不在本定理范围内。一般模型上「全部 AxiomC 的
  空间」仍未分类，如实保留。

纪律：零新增 axiom、零 sorry；只 import 既有模块；
      不修改 CSQIT_W1 / CSQIT_Enhanced / 既有 V1Bridge 文件。
================================================================================ -/

import CSQIT_V1Bridge.LayerWitness
import Mathlib.NumberTheory.Real.Irrational

namespace CSQIT_V1Bridge

open CSQIT_W1.CompilerAxioms
open CSQIT_W1.Foundation
open Complex
open Real

/-! ============================================================================
    §0. 单位根谓词
   ============================================================================ -/

/-- **单位根谓词（自定义）**：`c` 是（正次数）单位根。
    不依赖 Mathlib 的 `IsRootOfUnity` 命名；语义即「存在 `n > 0` 使
    `c ^ n = 1`」。 -/
def IsRootOfUnityC (c : ℂ) : Prop := ∃ n : ℕ, 0 < n ∧ c ^ n = 1

/-! ============================================================================
    §1. 递归展开：一个点决定整个振幅层
   ============================================================================ -/

/-- **递归步（W1，A 档）**：在 `compose a b = a+b+1` 的模型上，
    `amplitude (n+1) = amplitude n · amplitude 0`。

    证明：`n + 1 = compose n 0`，由 `comp_rule` 乘法性。 -/
theorem amplitude_succ_of_witness_compose {A : AxiomA ℕ ℕ}
    (hcomp : ∀ a b : ℕ, A.compose a b = a + b + 1)
    (Cx : @AxiomC ℕ ℕ A) (n : ℕ) :
    Cx.amplitude (n + 1) = Cx.amplitude n * Cx.amplitude 0 := by
  have h : Cx.amplitude (A.compose n 0) = Cx.amplitude n * Cx.amplitude 0 :=
    Cx.comp_rule n 0
  rw [hcomp n 0] at h
  simpa using h

/-- **G24a（W1，A 档，分类主引理）**：在 `compose a b = a+b+1` 的模型上，
    任何 `AxiomC` 的振幅都是 `c^(n+1)`，其中 `c := amplitude 0`。

    **一个点决定整个振幅层**：乘法性 + 归纳，无其他自由度。 -/
theorem amplitude_eq_pow_of_witness_compose {A : AxiomA ℕ ℕ}
    (hcomp : ∀ a b : ℕ, A.compose a b = a + b + 1)
    (Cx : @AxiomC ℕ ℕ A) (n : ℕ) :
    Cx.amplitude n = Cx.amplitude 0 ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [amplitude_succ_of_witness_compose hcomp Cx n, ih]
    exact (pow_succ (Cx.amplitude 0) (n + 1)).symm

/-! ============================================================================
    §2. 单位根判据与构造方向
   ============================================================================ -/

/-- 幂函数 `n ↦ c^(n+1)` 在 `c ≠ 0`、非单位根时的单射性（辅助引理：
    若 `c^(a+1) = c^(b+1)` 且 `a ≤ b`，则 `b = a` 或 `c` 是单位根）。 -/
private lemma pow_eq_absorbs_le {c : ℂ} (hc0 : c ≠ 0)
    (hnot : ¬ IsRootOfUnityC c) {a b : ℕ} (hle : a ≤ b)
    (h : c ^ (a + 1) = c ^ (b + 1)) : a = b := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  by_cases hk0 : k = 0
  · omega
  · exfalso
    -- c^(b+1) = c^((a+k)+1) = c^((a+1)+k) = c^(a+1) · c^k
    have hexp : (b : ℕ) + 1 = (a + 1) + k := by omega
    have h2 : c ^ ((a + 1) + k) = c ^ (a + 1) := by
      rw [← hexp]
      exact h.symm
    rw [pow_add] at h2
    -- c^(a+1) · c^k = c^(a+1) → c^k = 1（c^(a+1) ≠ 0）
    have hpos : 0 < k := by omega
    have hcancel : c ^ k = 1 := by
      have h3 : c ^ (a + 1) * c ^ k = c ^ (a + 1) * 1 :=
        h2.trans (mul_one (c ^ (a + 1))).symm
      exact mul_left_cancel₀ (pow_ne_zero (a + 1) hc0) h3
    exact hnot ⟨k, hpos, hcancel⟩

/-- **G24b（W1，A 档，单射判据）**：`|c| = 1` 时，
    `n ↦ c^(n+1)` 单射 ⟺ `c` 非单位根。 -/
theorem injective_pow_iff_not_root {c : ℂ} (hc : Complex.normSq c = 1) :
    Function.Injective (fun n : ℕ => c ^ (n + 1)) ↔ ¬ IsRootOfUnityC c := by
  constructor
  · -- 单射 ⇒ 非单位根
    rintro hinj ⟨N, hNpos, hroot⟩
    have h0 : c ^ ((0 : ℕ) + 1) = c ^ (N + 1) := by
      rw [pow_succ, pow_succ, hroot, pow_zero, one_mul]
    have hzero : (0 : ℕ) = N := hinj h0
    omega
  · -- 非单位根 ⇒ 单射
    intro hnot
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0] at hc
      simp at hc
    intro a b hab
    rcases le_total a b with hle | hle
    · exact pow_eq_absorbs_le hc0 hnot hle hab
    · exact (pow_eq_absorbs_le hc0 hnot hle hab.symm).symm

/-- **G24c（W1，A 档，构造方向）**：任何 `|c| = 1` 且非单位根的 `c`，
    反向给出见证 compose 上的合法 `AxiomC`。

    声明为 `def` 而非 `instance`：避免在 `ℕ ℕ` 上制造第二个默认
    `AxiomC` 实例（与 G20 的 `altAxiomC` 同一纪律）。 -/
@[implicit_reducible]
noncomputable def powAxiomC (c : ℂ) (hc : Complex.normSq c = 1)
    (hroot : ¬ IsRootOfUnityC c) : @AxiomC ℕ ℕ witnessAxiomA where
  amplitude := fun n => c ^ (n + 1)
  norm_one := by
    intro n
    induction n with
    | zero => simpa using hc
    | succ m ih =>
      rw [pow_succ, Complex.normSq_mul, ih, hc]
      norm_num
  comp_rule := by
    intro a b
    show c ^ ((a + b + 1 : ℕ) + 1) = c ^ (a + 1) * c ^ (b + 1)
    have hexp : (a + b + 1 : ℕ) + 1 = (a + 1) + (b + 1) := by omega
    rw [hexp, pow_add]
  amplitude_injective := (injective_pow_iff_not_root hc).mpr hroot

/-! ============================================================================
    §3. 相等判据：振幅层数据无冗余
   ============================================================================ -/

/-- **G24d（W1，A 档，相等判据）**：见证 compose 上两个 `AxiomC` 相等
    ⟺ 它们在 0 处的振幅相等。

    由 G24a（每点 = c^(n+1)）+ G10（作用量由振幅唯一重构），
    振幅层的全部信息恰为单点参数 `c`；结构无其他数据。 -/
theorem axiomC_eq_iff_zero_eq (Cx₁ Cx₂ : @AxiomC ℕ ℕ witnessAxiomA) :
    Cx₁ = Cx₂ ↔ Cx₁.amplitude 0 = Cx₂.amplitude 0 := by
  constructor
  · exact fun h => h ▸ rfl
  · intro h
    have hamp : Cx₁.amplitude = Cx₂.amplitude := by
      funext n
      rw [amplitude_eq_pow_of_witness_compose (A := witnessAxiomA) (by intro a b; rfl) Cx₁ n,
          amplitude_eq_pow_of_witness_compose (A := witnessAxiomA) (by intro a b; rfl) Cx₂ n, h]
    cases Cx₁ with
    | mk a₁ _ _ _ =>
      cases Cx₂ with
      | mk a₂ _ _ _ =>
        have hproj : a₁ = a₂ := hamp
        cases hproj
        rfl

/-! ============================================================================
    §4. 作用量参数化：S(n) = (n+1) • S(0)
   ============================================================================ -/

/-- **G24e（W1，A 档，作用量参数化）**：`powAxiomC c` 的作用量是
    生成元相位 `S(0)` 的整数倍：`S(n) = (n+1) • S(0)`。

    证明：`n + 1 = compose n 0`，由 `actionPhase_add` 递归。
    结合 G4（`actionPhase` 由振幅导出），作用量层无独立自由度。 -/
theorem actionPhase_powAxiomC_smul (c : ℂ) (hc : Complex.normSq c = 1)
    (hroot : ¬ IsRootOfUnityC c) (n : ℕ) :
    @actionPhase ℕ ℕ witnessAxiomA (powAxiomC c hc hroot) n =
      (n + 1 : ℕ) • (@actionPhase ℕ ℕ witnessAxiomA (powAxiomC c hc hroot) 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : @actionPhase ℕ ℕ witnessAxiomA (powAxiomC c hc hroot) (n + 1)
        = @actionPhase ℕ ℕ witnessAxiomA (powAxiomC c hc hroot) n
          + @actionPhase ℕ ℕ witnessAxiomA (powAxiomC c hc hroot) 0 := by
      have hadd := @actionPhase_add ℕ ℕ witnessAxiomA (powAxiomC c hc hroot) n 0
      exact hadd
    have hsmul : ((n + 1 : ℕ) + 1) •
        (@actionPhase ℕ ℕ witnessAxiomA (powAxiomC c hc hroot) 0) =
        (n + 1) • (@actionPhase ℕ ℕ witnessAxiomA (powAxiomC c hc hroot) 0) +
          (@actionPhase ℕ ℕ witnessAxiomA (powAxiomC c hc hroot) 0) := by
      rw [add_smul, one_smul]
    rw [hstep, ih]
    exact hsmul.symm

/-! ============================================================================
    §5. 见证实例化
   ============================================================================ -/

/-- `Circle.exp a` 的 `n` 次幂（辅助引理）。 -/
private lemma circle_exp_pow (a : ℝ) (n : ℕ) :
    ((Circle.exp a : Circle) : ℂ) ^ n = ((Circle.exp ((n : ℝ) * a) : Circle) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hdist : (((n + 1 : ℕ) : ℝ)) * a = (n : ℝ) * a + a := by
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    rw [pow_succ, ih, hdist, ← Circle.coe_mul, ← Circle.exp_add]

/-- **G24f（W1，A 档）**：见证振幅的单点参数 `c = exp(iπ√2)` 非单位根。

    这确认 witnessAxiomC 落在分类空间（圆 ∖ 单位根）内，不是退化解。 -/
theorem witness_not_root : ¬ IsRootOfUnityC (witnessAxiomC.amplitude 0) := by
  rintro ⟨N, hNpos, hroot⟩
  have h0 : witnessAxiomC.amplitude 0 = ((Circle.exp witnessAngle : Circle) : ℂ) := by
    change witnessAmplitude 0 = _
    simp [witnessAmplitude]
  rw [h0, circle_exp_pow] at hroot
  have hcirc : (Circle.exp ((N : ℝ) * witnessAngle) : Circle) = 1 :=
    Subtype.ext hroot
  obtain ⟨m, hm⟩ := Circle.exp_eq_one.mp hcirc
  have hpi_ne : (π : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  have hval : ((N : ℝ) * Real.sqrt 2) = (m : ℝ) * 2 := by
    unfold witnessAngle at hm
    field_simp [hpi_ne] at hm
    ring_nf at hm
    linarith
  have hNpos' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos'
  have hcomm : Real.sqrt 2 * (N : ℝ) = (m : ℝ) * 2 := by
    rw [mul_comm]
    exact hval
  have hval2 : Real.sqrt 2 = ((m : ℝ) * 2) / (N : ℝ) := by
    rw [eq_div_iff hNne]
    linarith
  have hq : Real.sqrt 2 = (((2 * (m : ℚ)) / ((N : ℚ)) : ℚ) : ℝ) := by
    rw [hval2]
    push_cast
    ring
  exact irrational_sqrt_two ⟨_, hq.symm⟩

/-- **G24g（W1，A 档）**：见证实例回填分类：`witnessAmplitude n = c^(n+1)`，
    其中 `c = witnessAmplitude 0 = exp(iπ√2)`。

    与 `GaugeAndEndo.altAxiomC`（`c' = exp(2iπ√2) = c²`）一起，
    G20 的两个实例都是同一分类空间的成员；分类空间除此之外
    还含全部非单位根圆点——但再无其他类型的自由度。 -/
theorem witnessAmplitude_eq_pow (n : ℕ) :
    witnessAxiomC.amplitude n = witnessAxiomC.amplitude 0 ^ (n + 1) :=
  amplitude_eq_pow_of_witness_compose (A := witnessAxiomA) (by intro a b; rfl)
    witnessAxiomC n

/-! ============================================================================
    汇总：G24 四档

  新增结论（全部 W1、零新增公设、零 sorry）：

    G24a  分类主引理：amplitude n = amplitude 0 ^ (n+1)（一个点决定全层）
    G24b  单射判据：n ↦ c^(n+1) 单射 ⟺ c 非单位根（|c|=1）
    G24c  构造方向：非单位根圆点 c 反向给出 AxiomC（powAxiomC）
    G24d  相等判据：AxiomC 相等 ⟺ 0 处振幅相等（数据无冗余）
    G24e  作用量参数化：S(n) = (n+1) • S(0)（作用量层无独立自由度）
    G24f  见证参数非单位根（exp(iπ√2) 落在分类空间内）
    G24g  见证实例回填分类

  档位：全部 A 档（在既有 AxiomA/AxiomC 定义上直接陈述并证明）。

  信息增益：
    1. 完成 G20 从「存在两个」到「全部枚举」的升级：见证 compose 上的
       振幅层 = {c^(n+1) : c ∈ 圆, c 非单位根}，与 {c} 一一对应。
    2. 回答「振幅层还能挖出什么」：不能——它是一个单参数层，
       全部内容 = 单点相位的整数倍扫描（G24a/e）。
    3. 边界如实登记：分类只在 compose = a+b+1 的模型上成立；
       一般模型上 AxiomC 空间的分类未做，不声称。
================================================================================ -/

end CSQIT_V1Bridge
