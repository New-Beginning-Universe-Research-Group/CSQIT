/-
================================================================================
CSQIT_V1Bridge — 作用量的规范自由度与见证模型的自同态（G20–G21）
模块: CSQIT_V1Bridge.GaugeAndEndo
版本: v0.1.0（2026-11-07）
================================================================================

承接 `BOUNDARIES.md` §14（停在 G19：amplitude 不能是有限阶单位根）。
§14 的结论是：给定**一个** amplitude，作用量 S 唯一（G10），且其值域
不能有限（G19）。剩下一个未问的问题：

  V1 A5「测度刚性」若翻译成 v23 语言，至少要求「作用量由因果/组合结构
  决定」。这个翻译能否成立？

本模块给出**否定式**回答，并刻画承载该层的见证模型的自同态：

  §1 一般引理：对任意无理数 s，`n ↦ exp(i(n+1)·π·s)` 是单射。
      （既有 `LayerWitness` 只证了 s = √2 的特例；这里把它一般化。）
  §2 G20：同一 `compose`（`a+b+1`）上存在两个不同的 `AxiomC` 结构：
      `amplitude n = exp(i(n+1)·π√2)` 与 `exp(i(n+1)·π·2√2)`。
      两者振幅在 0 处不同，因此作用量 `actionPhase` 也不同。
      结论（A 档，否定）：**S 不是由 compose / 因果结构决定的**；
      A5 的「S 由同构类决定」在 v23 的唯一可用通道上不成立。
      注意：这不与 G10 冲突——G10 说的是「给定 amplitude，S 唯一」；
      本模块说的是「amplitude 本身不是 compose 的函数」。
  §3 G21：见证模型 `(ℕ, a+b+1)` 的自同态完全分类：
      `φ(n) = φ(0) + n·(φ(0)+1)`。
      因此：φ(0)=0 ⇒ φ = id；φ(0)>0 ⇒ φ 严格递增、单射、不满射
      （像一次「粗粒化嵌入」），且在 0 处改变振幅。
      结论（A 档）：非平凡自同态存在，但**没有任何非平凡自同态保振幅**；
      RG 流若要以 compose-自同态实现，必须改变 S。

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
    §1. 一般引理：无理相位给出单射振幅族
   ============================================================================ -/

/-- **无理相位族的单射性（W1，A 档）**：若 `s` 无理，则
    `n ↦ exp(i·(n+1)·π·s)` 是 `ℕ → ℂ` 的单射。

    这是 `LayerWitness` 中 `witnessAxiomC.amplitude_injective` 的一般化：
    那里只证了 `s = √2`；这里对任意无理 `s` 成立，且证明结构相同——
    把 `√2` 换成 `s`，把 `irrational_sqrt_two` 换成假设 `hs`。 -/
theorem circleAmplitude_injective_of_irrational (s : ℝ) (hs : Irrational s) :
    Function.Injective
      (fun n : ℕ => (Circle.exp (((n : ℝ) + 1) * (π * s)) : ℂ)) := by
  intro a b h
  have hcirc : Circle.exp (((a : ℝ) + 1) * (π * s)) =
      Circle.exp (((b : ℝ) + 1) * (π * s)) := Subtype.ext h
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hcirc
  have h1 : ((a : ℝ) - (b : ℝ)) * (π * s) = (m : ℝ) * (2 * π) := by
    calc
      ((a : ℝ) - (b : ℝ)) * (π * s)
          = (((a : ℝ) + 1) - ((b : ℝ) + 1)) * (π * s) := by ring
      _ = ((a : ℝ) + 1) * (π * s) - ((b : ℝ) + 1) * (π * s) := by ring
      _ = (m : ℝ) * (2 * π) := by linarith
  have hpi_ne : (π : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  have hdiv := congrArg (fun x : ℝ => x / π) h1
  have hs_eq : ((a : ℝ) - (b : ℝ)) * s = (m : ℝ) * 2 := by
    field_simp [hpi_ne] at hdiv
    ring_nf at hdiv
    linarith
  by_cases hab : a = b
  · exact hab
  · have hdiff : (a : ℝ) - (b : ℝ) ≠ 0 := by
      intro h0
      have hcast : (a : ℝ) = (b : ℝ) := sub_eq_zero.mp h0
      exact hab (Nat.cast_injective hcast)
    have hs_val : s = ((m : ℝ) * 2) / ((a : ℝ) - (b : ℝ)) := by
      field_simp [hdiff]
      ring_nf
      linarith
    have hq : s = (((2 * (m : ℚ)) / ((a : ℚ) - (b : ℚ)) : ℚ) : ℝ) := by
      rw [hs_val]
      push_cast
      ring
    exact (hs ⟨_, hq.symm⟩).elim

/-- `2√2` 是无理数（由 `√2` 无理，且除以 2 保持有理）。 -/
theorem two_sqrt_two_irrational : Irrational (2 * Real.sqrt 2) := by
  intro h
  obtain ⟨q, hq⟩ := h
  have hq' : (q : ℝ) = 2 * Real.sqrt 2 := hq
  refine irrational_sqrt_two ⟨q / 2, ?_⟩
  push_cast
  linarith

/-! ============================================================================
    §2. G20：同一 compose 上的两个 AxiomC 结构
   ============================================================================ -/

/-- 第二个相位角：`π·(2√2)`（见证模型相位角的两倍）。 -/
noncomputable def doubleWitnessAngle : ℝ := π * (2 * Real.sqrt 2)

/-- 备选振幅：`n ↦ exp(i·(n+1)·π·2√2)`。 -/
noncomputable def altAmplitude (n : ℕ) : ℂ :=
  (Circle.exp (((n : ℝ) + 1) * doubleWitnessAngle) : ℂ)

/-- **备选 `AxiomC` 结构（A 档，存在性）**：与 `witnessAxiomC` 共用同一个
    `AxiomA`（即 `compose a b = a+b+1`），但振幅不同。

    注意这里刻意声明为 `def` 而不是 `instance`：避免在 `ℕ ℕ` 上出现两个
    `AxiomC` 实例、污染既有引理的 typeclass 解析。 -/
@[implicit_reducible]
noncomputable def altAxiomC : AxiomC ℕ ℕ where
  amplitude := altAmplitude
  norm_one := by
    intro n
    have hnorm : ‖(Circle.exp (((n : ℝ) + 1) * doubleWitnessAngle) : ℂ)‖ = 1 :=
      Circle.norm_coe _
    rw [altAmplitude, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  comp_rule := by
    intro a b
    change (Circle.exp ((((a + b + 1 : ℕ) : ℝ) + 1) * doubleWitnessAngle) : ℂ) =
      (Circle.exp (((a : ℝ) + 1) * doubleWitnessAngle) : ℂ) *
        (Circle.exp (((b : ℝ) + 1) * doubleWitnessAngle) : ℂ)
    have harg : ((((a + b + 1 : ℕ) : ℝ) + 1) * doubleWitnessAngle) =
        ((a : ℝ) + 1) * doubleWitnessAngle + ((b : ℝ) + 1) * doubleWitnessAngle := by
      unfold doubleWitnessAngle
      push_cast
      ring
    rw [harg, Circle.exp_add]
    simp
  amplitude_injective := by
    intro a b h
    exact circleAmplitude_injective_of_irrational (2 * Real.sqrt 2)
      two_sqrt_two_irrational (by simpa [altAmplitude, doubleWitnessAngle] using h)

/-- **G20a（W1，A 档）**：备选振幅在 0 处等于见证振幅的平方。 -/
theorem altAmplitude_zero_eq_sq :
    altAmplitude 0 = witnessAmplitude 0 * witnessAmplitude 0 := by
  have hangle : doubleWitnessAngle = witnessAngle + witnessAngle := by
    unfold doubleWitnessAngle witnessAngle
    ring
  have harg : ((((0 : ℕ) : ℝ) + 1) * (witnessAngle + witnessAngle)) =
      ((((0 : ℕ) : ℝ) + 1) * witnessAngle) +
        ((((0 : ℕ) : ℝ) + 1) * witnessAngle) := by ring
  have hc : Circle.exp ((((0 : ℕ) : ℝ) + 1) * doubleWitnessAngle) =
      Circle.exp ((((0 : ℕ) : ℝ) + 1) * witnessAngle) *
        Circle.exp ((((0 : ℕ) : ℝ) + 1) * witnessAngle) := by
    rw [hangle, harg, Circle.exp_add]
  have hcoe := congrArg (fun z : Circle => (z : ℂ)) hc
  simpa [altAmplitude, witnessAmplitude, Circle.coe_mul] using hcoe

/-- **G20b（W1，A 档）**：备选振幅与见证振幅在 0 处不同。

    `alt(0) = z²`，`witness(0) = z`；由 `z ≠ 0` 与 `z ≠ 1` 得 `z² ≠ z`。
    因此这不是「同一振幅的另一种写法」，而是实质不同的振幅数据。 -/
theorem altAmplitude_zero_ne_witness :
    altAmplitude 0 ≠ witnessAmplitude 0 := by
  intro h
  have hsq : altAmplitude 0 = witnessAmplitude 0 * witnessAmplitude 0 :=
    altAmplitude_zero_eq_sq
  have hz0 : witnessAmplitude 0 ≠ 0 := by
    unfold witnessAmplitude
    exact Circle.coe_ne_zero _
  have hz1 : witnessAmplitude 0 ≠ 1 := witness_amplitude_zero_ne_one
  have hsub : witnessAmplitude 0 * witnessAmplitude 0 - witnessAmplitude 0 ≠ 0 := by
    have hfac : witnessAmplitude 0 * witnessAmplitude 0 - witnessAmplitude 0 =
        witnessAmplitude 0 * (witnessAmplitude 0 - 1) := by ring
    rw [hfac]
    exact mul_ne_zero hz0 (sub_ne_zero.mpr hz1)
  exact hsub (sub_eq_zero.mpr (hsq.symm.trans h))

/-- **G20c（W1，A 档，否定）**：在同一个 `compose` 结构上，存在两个不同的
    `AxiomC` 实例。这是「振幅不是 compose 的函数」的精确陈述。 -/
theorem exists_amplitude_variation :
    ∃ Cx₁ Cx₂ : AxiomC ℕ ℕ, Cx₁.amplitude 0 ≠ Cx₂.amplitude 0 := by
  refine ⟨witnessAxiomC, altAxiomC, ?_⟩
  change witnessAmplitude 0 ≠ altAmplitude 0
  exact fun h => altAmplitude_zero_ne_witness h.symm

/-- **相位由振幅唯一决定（W1，A 档）**：两个 `AxiomC` 结构若在同一点给出
    不同的振幅，则它们的作用量 `actionPhase` 在该点也不同。

    证明：`actionPhase_reconstructs_amplitude` 把相位重新包成振幅，
    再用 `Real.Angle.toCircle` 的单射性。
    这条把「振幅差异」提升为「作用量差异」，是 G20 的关键桥梁。 -/
theorem actionPhase_ne_of_amplitude_ne {M C : Type*} [A : AxiomA M C]
    {Cx₁ Cx₂ : AxiomC M C} (α : C)
    (h : Cx₁.amplitude α ≠ Cx₂.amplitude α) :
    @actionPhase M C A Cx₁ α ≠ @actionPhase M C A Cx₂ α := by
  intro heq
  apply h
  have hcongr : (Real.Angle.toCircle (@actionPhase M C A Cx₁ α) : ℂ) =
      (Real.Angle.toCircle (@actionPhase M C A Cx₂ α) : ℂ) :=
    congrArg (fun θ : Real.Angle => (Real.Angle.toCircle θ : ℂ)) heq
  calc
    Cx₁.amplitude α
        = (Real.Angle.toCircle (@actionPhase M C A Cx₁ α) : ℂ) :=
          (@actionPhase_reconstructs_amplitude M C A Cx₁ α).symm
    _ = (Real.Angle.toCircle (@actionPhase M C A Cx₂ α) : ℂ) := hcongr
    _ = Cx₂.amplitude α := @actionPhase_reconstructs_amplitude M C A Cx₂ α

/-- **G20d（W1，A 档，否定）**：作用量不是由 `compose` / 因果结构决定的。

    同一 `AxiomA`（`ℕ, a+b+1`）上存在两个 `AxiomC`，其作用量在 0 处不同。
    因此 A5「S 由同构类/因果结构决定」不能在 v23 中作为定理成立：
    S 是额外的 U(1) 数据，不是 compose 的函数。

    边界：这不否定「给定 amplitude 时 S 唯一」（G10 已证唯一且 c = 0），
    也不声称 V1 A5 的完整测度论语义为假——它仍是 C 档诠释假设。
    本条是否定其**最小代数翻译**。 -/
theorem actionPhase_not_determined_by_compose :
    ∃ Cx₁ Cx₂ : AxiomC ℕ ℕ,
      (@actionPhase ℕ ℕ witnessAxiomA Cx₁ 0) ≠
        (@actionPhase ℕ ℕ witnessAxiomA Cx₂ 0) := by
  refine ⟨witnessAxiomC, altAxiomC, ?_⟩
  apply actionPhase_ne_of_amplitude_ne (A := witnessAxiomA)
    (Cx₁ := witnessAxiomC) (Cx₂ := altAxiomC) (α := 0)
  change witnessAmplitude 0 ≠ altAmplitude 0
  exact fun h => altAmplitude_zero_ne_witness h.symm

/-! ============================================================================
    §3. G21：见证模型的自同态分类
   ============================================================================ -/

/-- **G21a（W1，A 档，分类）**：`(ℕ, a+b+1)` 的任意自同态都是仿射形
    `φ(n) = φ(0) + n·(φ(0)+1)`。

    证明只用递归式 `φ(n+1) = φ(0) + φ(n) + 1`（由 `h` 取 `a=0`），
    再对 n 归纳；完全不需要交换律之外的额外结构。 -/
theorem witnessEndo_classification (φ : ℕ → ℕ)
    (h : ∀ a b : ℕ, φ (a + b + 1) = φ a + φ b + 1) :
    ∀ n : ℕ, φ n = φ 0 + n * (φ 0 + 1) := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
    have hstep : φ (n + 1) = φ 0 + φ n + 1 := by
      have h0 := h 0 n
      simpa using h0
    rw [hstep, ih]
    ring

/-- 自同态条件的算术形式（由 `compose` 形式展开）。 -/
theorem witnessEndo_arith_of_compose (φ : ℕ → ℕ)
    (h : ∀ a b : ℕ, φ (witnessAxiomA.compose a b) = witnessAxiomA.compose (φ a) (φ b)) :
    ∀ a b : ℕ, φ (a + b + 1) = φ a + φ b + 1 := by
  intro a b
  simpa using h a b

/-- **G21b（W1，A 档）**：自同态保振幅当且仅当 `φ(0) = 0`（即 `φ = id`）。

    正向只看 `n = 0`：`amplitude (φ 0) = amplitude 0`，由振幅单射得
    `φ 0 = 0`；反向由分类定理得 `φ n = n`。
    这把「非平凡自同态」与「改变振幅」绑定：不存在保振幅的非平凡自同态。 -/
theorem witnessEndo_amplitude_iff (φ : ℕ → ℕ)
    (h : ∀ a b : ℕ, φ (a + b + 1) = φ a + φ b + 1) :
    (∀ n : ℕ, witnessAxiomC.amplitude (φ n) = witnessAxiomC.amplitude n) ↔
      φ 0 = 0 := by
  constructor
  · intro hamp
    exact witnessAxiomC.amplitude_injective (hamp 0)
  · intro h0 n
    have hcls := witnessEndo_classification φ h n
    have hid : φ n = n := by
      rw [hcls, h0]
      ring
    rw [hid]

/-- 具体的非平凡自同态：`n ↦ 2n+1`（对应 `φ(0)=1`）。 -/
def doubleEndo (n : ℕ) : ℕ := 2 * n + 1

/-- `doubleEndo` 满足自同态条件。 -/
theorem doubleEndo_arith :
    ∀ a b : ℕ, doubleEndo (a + b + 1) = doubleEndo a + doubleEndo b + 1 := by
  intro a b
  unfold doubleEndo
  omega

/-- `doubleEndo` 单射。 -/
theorem doubleEndo_injective : Function.Injective doubleEndo := by
  intro a b h
  unfold doubleEndo at h
  omega

/-- **G21c（W1，A 档）**：`doubleEndo` 严格递增：非平凡自同态不是塌缩映射，
    而是保序嵌入。 -/
theorem doubleEndo_strictMono : StrictMono doubleEndo := by
  intro a b hab
  unfold doubleEndo
  omega

/-- **G21d（W1，A 档，否定）**：`doubleEndo` 不满射（0 不在像中）。
    因此它给出一次真正的「粗粒化嵌入」：像比原载体稀疏。 -/
theorem doubleEndo_not_surjective : ¬ Function.Surjective doubleEndo := by
  intro hsurj
  obtain ⟨n, hn⟩ := hsurj 0
  unfold doubleEndo at hn
  omega

/-- **G21e（W1，A 档，否定）**：`doubleEndo` 不保振幅。 -/
theorem doubleEndo_not_amplitude_preserving :
    ¬ ∀ n : ℕ, witnessAxiomC.amplitude (doubleEndo n) = witnessAxiomC.amplitude n := by
  intro hamp
  have h0 : doubleEndo 0 = 0 := witnessAxiomC.amplitude_injective (hamp 0)
  unfold doubleEndo at h0
  omega

/-- **G21f（W1，A 档）**：见证模型上存在非平凡、保序、单射、不满射的自同态，
    且它必然改变振幅。

    结构含义：若把「RG 粗粒化」翻译为 compose-自同态，那么在 v23 中
    可以存在非平凡流（`n ↦ 2n+1`），但它**不能保振幅**；
    再结合 G12（任意保振幅自映射必为恒等），得到：
    「保 S 的 RG 流」在振幅层上不存在；任何非平凡流都必须改变 S。
    这不等于「RG 流已被证否」——V1 A2 的完整尺度语义仍为 C 档。 -/
theorem witnessEndo_nontrivial_exists :
    ∃ φ : ℕ → ℕ,
      (∀ a b : ℕ, φ (a + b + 1) = φ a + φ b + 1) ∧
        Function.Injective φ ∧ ¬ Function.Surjective φ ∧
          ¬ ∀ n : ℕ, witnessAxiomC.amplitude (φ n) = witnessAxiomC.amplitude n :=
  ⟨doubleEndo, doubleEndo_arith, doubleEndo_injective, doubleEndo_not_surjective,
    doubleEndo_not_amplitude_preserving⟩

/-! ============================================================================
    汇总：G20–G21 四档

  新增结论（全部 A 档、零新增公设、零 sorry）：

    G20a/20b  同一 compose 上两个 AxiomC：alt(0) = witness(0)² ≠ witness(0)
    G20c      存在振幅差异的 AxiomC 对（振幅不是 compose 的函数）
    G20d      作用量 actionPhase 也随之不同（S 不由因果结构决定）
    G21a      见证模型自同态完全分类：φ(n) = φ(0) + n·(φ(0)+1)
    G21b      自同态保振幅 ⇔ φ(0)=0 ⇔ φ=id
    G21c–e    n↦2n+1：严格递增、单射、不满射、不保振幅
    G21f      非平凡自同态存在，但全部改变振幅

  信息增益：
    1. 把 V1 A5（测度刚性）的最小代数翻译明确判为「不能由因果结构导出」：
       S 是额外数据，不是 compose 的函数。与 G10 合起来是完整图景：
       「给定振幅 → S 唯一；但振幅本身不被 compose 决定」。
    2. 把 G12「保振幅 ⇒ 恒等」升级为「自同态全分类 + 非平凡流存在但必改 S」，
       从而把 RG 流的最小实现边界钉死。
================================================================================ -/

end CSQIT_V1Bridge
