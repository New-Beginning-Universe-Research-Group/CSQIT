/-
================================================================================
CSQIT_V1Bridge — 因果-振幅层的非空洞见证与三条收口定理
模块: CSQIT_V1Bridge.LayerWitness
版本: v0.1.0（2026-11-07）
================================================================================

上一轮（G1–G7）已把因果-振幅层刻画为
  `Nonempty layer ↔ 无右作用元`
且证明有限载体不可能承载该层（G7）。剩下两个未闭合的缺口：

  (1) G7 只给了**必要性**（有限载体不行），没有给出**存在性**：
      若「无限 + 无右作用元 + 振幅单射」本身不相容，则 G1′/G5 的
      条件层就是空条件。本模块构造一个具体的非空洞模型：
        C = ℕ, compose a b = a + b + 1, amplitude n = exp(i(n+1)·π√2)
      证明它同时满足 AxiomA、AxiomC（振幅单射、单位模、乘法性），
      且无右作用元，因此承载 V1 因果-振幅层。
      振幅单射性归约为 `√2` 无理（`irrational_sqrt_two`）；选用 θ = π√2
      而非 θ = 1，是为了在 exp 等式中让 π 直接约去。

  (2) 22 号 §7 G4 留下的「生成元上的唯一性」：实际上不需要生成元假设。
      只要 S 重构 amplitude，就与 `actionPhase` 逐点相等
      （`Real.Angle.toCircle` 单射）；故 G4 的唯一性是无条件 A 档，
      且比原计划的「相差常数 c」更强（c = 0）。

  (3) G2 只证了「存在性不可导」；唯一性那一半在 v23 依赖 AxiomC 的
      振幅单射。本模块补一个五字段层面的否定：
      纯 `CompilerAxiom` 下唯一性也不成立（左投影模型每点都是不动点）。
      即 V1「存在唯一」的两半都各有独立来源：唯一性来自 AxiomC，
      存在性需要额外的收缩/完备结构。

另有一条结构性引理：G1′ 构造的可达序是所有相容严格偏序中**最小**的
（任何相容序都包含可达关系）。这把「条件构造」从「某一个序」升级为
「该模型类上的典范最小序」。

纪律：零新增 axiom、零 sorry；只新增本文件与 lakefile 一行；
      不修改 CSQIT_W1 / CSQIT_Enhanced / 既有 V1Bridge 文件。
================================================================================ -/

import CSQIT_V1Bridge.CausalLayerSharpening
import Mathlib.NumberTheory.Real.Irrational

namespace CSQIT_V1Bridge

open CSQIT_W1.CompilerAxioms
open CSQIT_W1.Foundation
open Complex
open Real

/-! ============================================================================
    §1. 可达序的最小性
   ============================================================================ -/

/-- **可达序最小性（W1，A 档）**：在任意 `CompilerAxiom` 模型上，
    任何与 `compose` 相容的严格偏序 `r` 都包含「α 可达 β」关系。

    即 G1′ 构造的 `α ≺ β := ∃ γ, β = α∘γ ∧ β ≠ α` 是所有相容严格偏序中
    最细/最小的一个：它不依赖模型类假设，也不需要 `no-right-id`。
    这条把 G1′ 从「给出一个序」升级为「给出典范最小序」。 -/
theorem reachable_subset_of_compatible {M C : Type*} (CA : CompilerAxiom M C)
    {r : C → C → Prop} (h : CompatibleStrictOrder CA r) :
    ∀ {x y : C}, (∃ z : C, y = CA.compose x z ∧ y ≠ x) → r x y := by
  rintro x y ⟨z, hy, _⟩
  have hc : r x (CA.compose x z) := h.compat x z
  rwa [← hy] at hc

/-- **可达序最小性的层版本（W1，A 档）**：若层已给定，则它的因果序
    同样包含可达关系。直接由 `CompatibleStrictOrder` 实例化。 -/
theorem layer_reachable_subset {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (layer : V1CausalAmplitudeLayer (M := M) (C := C)) :
    ∀ {x y : C}, (∃ z : C, y = A.compose x z ∧ y ≠ x) → layer.causalOrder x y := by
  rintro x y ⟨z, hy, _⟩
  have hc : layer.causalOrder x (A.compose x z) := layer.compat x z
  rwa [← hy] at hc

/-! ============================================================================
    §2. G4 剩余项：作用量重构振幅 ⇒ 唯一（无需生成元假设）
   ============================================================================ -/

/-- **作用量唯一性（W1，A 档）**：任何 `S : C → Real.Angle`，只要它重构出
    与 `actionPhase` 相同的振幅，就逐点等于 `actionPhase`。

    证明：两边取 `toCircle` 后相同，`Real.Angle.toCircle` 单射。
    注意这里**不需要**先假设 S 的加法性，也不需要「由单个生成元覆盖」
    这一模型假设；因此 22 号 §7 G4 的「相差常数 c」实际上是 c = 0。 -/
theorem actionPhase_unique {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (S : C → Real.Angle)
    (hS : ∀ α : C, (Real.Angle.toCircle (S α) : ℂ) = Cx.amplitude α) :
    S = @actionPhase M C A Cx := by
  funext α
  have hinj : Function.Injective (@Real.Angle.toCircle) := by
    intro x y hxy
    have harg := congrArg
      (fun z : Circle => (Complex.arg (z : ℂ) : Real.Angle)) hxy
    simpa using harg
  apply hinj
  apply Subtype.ext
  rw [hS α, @actionPhase_reconstructs_amplitude M C A Cx α]

/-! ============================================================================
    §3. G2 剩余项：五字段下的不动点唯一性同样不成立
   ============================================================================ -/

/-- **五字段唯一性否定（W1，A 档）**：`CompilerAxiom` 不保证自指不动点唯一。

    反例是左投影模型：`compose a b = a`，故对每个 α 都有 `α∘α = α`。
    因此 V1「存在且唯一」的唯一性一半也不能由五字段得到；v23 的
    `weave_fixed_point_unique` 之所以成立，是因为它额外用了
    `AxiomC.amplitude_injective`。 -/
theorem no_uniform_fixed_point_unique_five :
    ¬ ∀ CA : CompilerAxiom ℕ ℕ, ∃! α : ℕ, CA.compose α α = α := by
  intro h
  obtain ⟨α, _, huniq⟩ := h leftProjection
  have h0 : leftProjection.compose 0 0 = 0 := rfl
  have h1 : leftProjection.compose 1 1 = 1 := rfl
  have e0 : (0 : ℕ) = α := huniq 0 h0
  have e1 : (1 : ℕ) = α := huniq 1 h1
  exact Nat.zero_ne_one (e0.trans e1.symm)

/-! ============================================================================
    §4. 非空洞见证：无限、无右作用元、振幅单射的模型

    载体 C = ℕ；compose a b = a + b + 1。
      · 结合律：omega
      · 无右作用元：a + b + 1 ≠ a
      · amplitude n = exp(i(n+1))：单位模、乘法性
        由 n ↦ n+1 的平移把 compose 的「+1」吸收掉；
        单射性等价于「exp(i·整数) 只有整数差为 0 才相等」，
        即 π 无理。
   ============================================================================ -/

/-- 见证模型的 `AxiomA` 实例：`compose a b = a + b + 1`。 -/
instance witnessAxiomA : AxiomA ℕ ℕ where
  input := fun _ => []
  output := fun _ => 0
  input_nodup := by
    intro _
    simp
  compose := fun a b => a + b + 1
  compose_input := by
    intro _ _
    simp
  compose_output := by
    intro _ _
    simp
  compose_assoc := by
    intro a b c
    omega

/-- 见证模型的相位角：`π√2`（选它而非 `1`，是为了在 exp 等式中让 π 约去，
    把单射性归约为 `√2` 无理）。 -/
noncomputable def witnessAngle : ℝ := π * Real.sqrt 2

/-- 见证模型的振幅：`n ↦ exp(i(n+1)·π√2)`。 -/
noncomputable def witnessAmplitude (n : ℕ) : ℂ :=
  (Circle.exp (((n : ℝ) + 1) * witnessAngle) : ℂ)

/-- 见证模型的 `AxiomC` 实例。 -/
noncomputable instance witnessAxiomC : AxiomC ℕ ℕ where
  amplitude := witnessAmplitude
  norm_one := by
    intro n
    have hnorm : ‖(Circle.exp (((n : ℝ) + 1) * witnessAngle) : ℂ)‖ = 1 :=
      Circle.norm_coe _
    rw [witnessAmplitude, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  comp_rule := by
    intro a b
    change (Circle.exp ((((a + b + 1 : ℕ) : ℝ) + 1) * witnessAngle) : ℂ) =
      (Circle.exp (((a : ℝ) + 1) * witnessAngle) : ℂ) *
        (Circle.exp (((b : ℝ) + 1) * witnessAngle) : ℂ)
    have harg : ((((a + b + 1 : ℕ) : ℝ) + 1) * witnessAngle) =
        ((a : ℝ) + 1) * witnessAngle + ((b : ℝ) + 1) * witnessAngle := by
      unfold witnessAngle
      push_cast
      ring
    rw [harg, Circle.exp_add]
    simp
  amplitude_injective := by
    intro a b h
    have hcirc : Circle.exp (((a : ℝ) + 1) * witnessAngle) =
        Circle.exp (((b : ℝ) + 1) * witnessAngle) := by
      simp only [witnessAmplitude] at h
      exact Subtype.ext h
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hcirc
    have h1 : ((a : ℝ) - (b : ℝ)) * witnessAngle = (m : ℝ) * (2 * π) := by
      calc
        ((a : ℝ) - (b : ℝ)) * witnessAngle
            = (((a : ℝ) + 1) - ((b : ℝ) + 1)) * witnessAngle := by ring
        _ = ((a : ℝ) + 1) * witnessAngle - ((b : ℝ) + 1) * witnessAngle := by ring
        _ = (m : ℝ) * (2 * π) := by linarith
    have hpi_ne : (π : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
    have hdiv := congrArg (fun x : ℝ => x / π) h1
    unfold witnessAngle at hdiv
    have hsqrt_eq : ((a : ℝ) - (b : ℝ)) * Real.sqrt 2 = (m : ℝ) * 2 := by
      field_simp [hpi_ne] at hdiv
      ring_nf at hdiv
      linarith
    by_cases hm0 : m = 0
    · have hsqrt_ne : (Real.sqrt 2 : ℝ) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos_of_pos (by norm_num))
      have hprod : ((a : ℝ) - (b : ℝ)) * Real.sqrt 2 = 0 := by
        simpa [hm0] using hsqrt_eq
      have hab : (a : ℝ) = (b : ℝ) := by
        rcases mul_eq_zero.mp hprod with h | h
        · linarith
        · exact absurd h hsqrt_ne
      exact Nat.cast_injective hab
    · have hmR : (m : ℝ) ≠ 0 := by
        exact_mod_cast hm0
      have hab_ne : (a : ℝ) - (b : ℝ) ≠ 0 := by
        intro hzero
        have hs := hsqrt_eq
        rw [hzero] at hs
        have hmz : (m : ℝ) = 0 := by
          linarith
        exact hmR hmz
      have hsqrt_val : Real.sqrt 2 =
          ((m : ℝ) * 2) / ((a : ℝ) - (b : ℝ)) := by
        field_simp [hab_ne]
        ring_nf
        linarith
      have hq : Real.sqrt 2 = (((2 * (m : ℚ)) / ((a : ℚ) - (b : ℚ)) : ℚ) : ℝ) := by
        rw [hsqrt_val]
        push_cast
        ring
      exact False.elim (irrational_sqrt_two ⟨_, hq.symm⟩)

/-- **见证模型无右作用元（W1）**：`a + b + 1 ≠ a`。 -/
theorem witness_no_right_id : ∀ x y : ℕ, witnessAxiomA.compose x y ≠ x := by
  intro x y h
  change x + y + 1 = x at h
  omega

/-- **G8（W1，A 档，存在性/非空洞性）**：在具体的无限模型
    `(ℕ, a+b+1, exp(i(n+1)·π√2))` 上，V1 因果-振幅层存在。

    这条补上 G7 只给必要性所缺的另一半：G1′/G5 的条件层不是空条件，
    且它可以与**单射的非平凡振幅**共存（不是靠退化振幅或外加的序）。
    因而「层要求无限载体」这一限制是实质的，而不是矛盾条件的伪装。 -/
theorem witness_layer_nonempty :
    Nonempty (V1CausalAmplitudeLayer (M := ℕ) (C := ℕ)) :=
  layer_constructible_on_no_right_id (M := ℕ) (C := ℕ) witness_no_right_id

/-- 见证模型上所有相位非零（由无右作用元 + G5 相位引理）。 -/
theorem witness_phase_ne_zero (n : ℕ) :
    (@actionPhase ℕ ℕ witnessAxiomA witnessAxiomC n) ≠ (0 : Real.Angle) :=
  no_right_id_implies_all_phases_nonzero (M := ℕ) (C := ℕ) witness_no_right_id n

/-- 见证模型的振幅确实非平凡：`amplitude 0 = exp(iπ√2)`，不是 1。 -/
theorem witness_amplitude_zero_ne_one :
    witnessAxiomC.amplitude 0 ≠ (1 : ℂ) := by
  change witnessAmplitude 0 ≠ (1 : ℂ)
  intro h
  have hcircle : Circle.exp witnessAngle = (1 : Circle) := by
    simp only [witnessAmplitude, Nat.cast_zero, zero_add, one_mul] at h
    exact Subtype.ext h
  obtain ⟨m, hm⟩ := Circle.exp_eq_one.mp hcircle
  have hm1 : witnessAngle = (m : ℝ) * (2 * π) := by
    simpa using hm
  have hpi_ne : (π : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  have hdiv := congrArg (fun x : ℝ => x / π) hm1
  unfold witnessAngle at hdiv
  have hsqrt : Real.sqrt 2 = (m : ℝ) * 2 := by
    field_simp [hpi_ne] at hdiv
    ring_nf at hdiv
    linarith
  have hq : Real.sqrt 2 = (((2 * (m : ℚ)) : ℚ) : ℝ) := by
    rw [hsqrt]
    push_cast
    ring
  exact irrational_sqrt_two ⟨_, hq.symm⟩

end CSQIT_V1Bridge
