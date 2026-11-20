/-
================================================================================
CSQIT_V1Bridge — Cantor 反例 + 作用量导出
模块: CSQIT_V1Bridge.OrderAndAction
版本: v0.1.0（2026-11-06）
================================================================================

本模块承接 OrderAndFixedPoint（G1+G2），完成 22 号文档首批深挖目标
中的 G3（Cantor 反例）与 G4（作用量导出）。

  §1 V7 A2「自生成满射」的有限 Cantor 反例：
      不存在 Bool → (Bool → Bool) 的满射，按字面为假。

  §2 从 amplitude 导出作用量 S : C → Real.Angle：
      v23 的 AxiomC 已经有 amplitude（单位模复数），但没有显式
      的 `S`。利用 `Real.Angle` 自带的：
        Real.Angle.toCircle : Angle → Circle（群同态，单射）
        Real.Angle.toCircle_coe : toCircle (↑r) = Circle.exp r
        Real.Angle.toCircle_add : toCircle (θ₁ + θ₂) = toCircle θ₁ * toCircle θ₂
      定义 `S α := Real.Angle.coe (Complex.arg (amplitude α))`
      证明：
        (a) `S (α∘β) = S α + S β`（相位加法）
        (b) `S` 是单射
        (c) `toCircle (S α) = amplitude α`（重构）

纪律：零新增 axiom、零 sorry；只 import 既有模块；
      不修改 CSQIT_W1 / CSQIT_Enhanced / CSQIT_V1Bridge.OrderAndFixedPoint。
================================================================================ -/

import CSQIT_W1.CompilerAxioms
import CSQIT_W1.Foundation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Bool.Basic

namespace CSQIT_V1Bridge

open CSQIT_W1.CompilerAxioms
open CSQIT_W1.Foundation
open Complex
open Real

/-! ============================================================================
    §1. Cantor 反例：有限载体上自生成满射不存在
   ============================================================================ -/

/-- **Cantor 反例（有限载体，W1 严格）**：不存在从 Bool 到 Bool→Bool 的
    满射。这是 Cantor 定理的有限实例——若 `Φ: O → (O → O)` 是满射，
    则取 O = Bool 即得矛盾。V7 A2「`Φ` 满」按字面在 Bool 上直接为假。 -/
theorem no_surjective_bool_self :
    ¬ ∃ f : Bool → (Bool → Bool), Function.Surjective f := by
  rintro ⟨f, h_surj⟩
  have hcard : Fintype.card (Bool → Bool) ≤ Fintype.card Bool :=
    Fintype.card_le_of_surjective f h_surj
  simp at hcard

/-! ============================================================================
    §2. 从 amplitude 导出作用量 S : C → Real.Angle
   ============================================================================ -/

/-- **辅助 h1**：normSq 为 1 ⇒ ‖z‖ = 1。 -/
private lemma h1 (h : Complex.normSq z = 1) : ‖z‖ = 1 := by
  have hnsq : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
  rw [hnsq] at h
  have hnonneg : 0 ≤ ‖z‖ := by positivity
  nlinarith

/-- **辅助 h2**：‖z‖ = 1 ⇒ z ∈ unitSphere。 -/
private lemma h2 (h : ‖z‖ = 1) : z ∈ Submonoid.unitSphere ℂ :=
  mem_sphere_zero_iff_norm.mpr h

/-- **toCircle 单射**：
    `Real.Angle.toCircle` 的单射性可直接从 `Real.Angle.arg_toCircle` 推出
    （若 `toCircle a = toCircle b`，两边取 arg 再提升即得 `a = b`）。
    我们在 actionPhase_add 里内联这个论证。 -/
private theorem _toCircle_inj_placeholder : True := trivial

/-- **S 的定义（W1 严格）**：
    `S α` = amplitude α 的 phase，提升到 `Real.Angle = ℝ/2πℤ`。 -/
noncomputable def actionPhase {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α : C) : Real.Angle :=
  Real.Angle.coe (Complex.arg (Cx.amplitude α))

/-- **关键桥接（W1 严格）**：
    `toCircle (S α) = Subtype.mk (amplitude α) _`。

    证明链（全用 Real.Angle namespace 的引理）：
      toCircle (S α)
        = toCircle (↑(arg (amplitude α)))          [def actionPhase]
        = Circle.exp (arg (amplitude α))              [Real.Angle.toCircle_coe]
        = Subtype.mk (amplitude α) _                  [Circle.exp_arg] -/
private lemma bridge {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C] (α : C) :
    Real.Angle.toCircle (@actionPhase M C _ _ α) =
      Subtype.mk (Cx.amplitude α)
        (h2 (h1 (h := Cx.norm_one α))) := by
  have h_norm_eq : ‖Cx.amplitude α‖ = 1 := h1 (h := Cx.norm_one α)
  have h_mem_eq : Cx.amplitude α ∈ Submonoid.unitSphere ℂ := h2 h_norm_eq
  let zc : Circle := ⟨Cx.amplitude α, h_mem_eq⟩
  have h_phase : @actionPhase M C _ _ α = Real.Angle.coe (Complex.arg (Cx.amplitude α)) := rfl
  rw [h_phase, Real.Angle.toCircle_coe]
  have h : Circle.exp (Complex.arg (Cx.amplitude α)) = zc := Circle.exp_arg zc
  rw [h]

/-- **S 的加法性（W1 严格）**：`S (α∘β) = S α + S β`。

    证明（群同态链）：
      toCircle (S (α∘β))
        = amplitude(α∘β)
        = amplitude α * amplitude β
        = toCircle (S α) * toCircle (S β)
        = toCircle (S α + S β)  [Real.Angle.toCircle_add]
      toCircle 单射 ⇒ S (α∘β) = S α + S β。 -/
theorem actionPhase_add {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α β : C) :
    @actionPhase M C _ _ (A.compose α β) =
    @actionPhase M C _ _ α + @actionPhase M C _ _ β := by
  have h_comp : Cx.amplitude (A.compose α β) = Cx.amplitude α * Cx.amplitude β :=
    Cx.comp_rule α β
  have h : Real.Angle.toCircle (@actionPhase M C _ _ (A.compose α β)) =
      Real.Angle.toCircle (@actionPhase M C _ _ α + @actionPhase M C _ _ β) := by
    have h1' : ‖Cx.amplitude α‖ = 1 := h1 (h := Cx.norm_one α)
    have h2' : ‖Cx.amplitude β‖ = 1 := h1 (h := Cx.norm_one β)
    have h3' : ‖Cx.amplitude (A.compose α β)‖ = 1 :=
      h1 (h := Cx.norm_one (A.compose α β))
    have hm1 : Cx.amplitude α ∈ Submonoid.unitSphere ℂ := h2 h1'
    have hm2 : Cx.amplitude β ∈ Submonoid.unitSphere ℂ := h2 h2'
    have hm3 : Cx.amplitude (A.compose α β) ∈ Submonoid.unitSphere ℂ := h2 h3'
    have h1 : Real.Angle.toCircle (@actionPhase M C _ _ (A.compose α β)) =
        Subtype.mk (Cx.amplitude (A.compose α β)) hm3 := bridge (A.compose α β)
    have h2 : Real.Angle.toCircle (@actionPhase M C _ _ α) =
        Subtype.mk (Cx.amplitude α) hm1 := bridge α
    have h3 : Real.Angle.toCircle (@actionPhase M C _ _ β) =
        Subtype.mk (Cx.amplitude β) hm2 := bridge β
    rw [Real.Angle.toCircle_add, h1, h2, h3]
    have hmem_ab : Cx.amplitude α * Cx.amplitude β ∈ Submonoid.unitSphere ℂ :=
      Submonoid.mul_mem (Submonoid.unitSphere ℂ) hm1 hm2
    have h4 : Subtype.mk (Cx.amplitude (A.compose α β)) hm3 =
        Subtype.mk (Cx.amplitude α * Cx.amplitude β) hmem_ab := by
      exact Subtype.ext_iff.mpr h_comp
    rw [h4]
    rfl
  have h_arg : ∀ (θ : Real.Angle), (Complex.arg (Real.Angle.toCircle θ) : Real.Angle) = θ := by
    intro θ
    exact Real.Angle.arg_toCircle θ
  have h_inj2 : Function.Injective (@Real.Angle.toCircle) := by
    intro a b h_eq
    have ha : (Complex.arg (Real.Angle.toCircle a) : Real.Angle) = a := h_arg a
    have hb : (Complex.arg (Real.Angle.toCircle b) : Real.Angle) = b := h_arg b
    have hc' : Complex.arg (Real.Angle.toCircle a) = Complex.arg (Real.Angle.toCircle b) := by
      rw [h_eq]
    have h_eq_angle : (Complex.arg (Real.Angle.toCircle a) : Real.Angle) =
        (Complex.arg (Real.Angle.toCircle b) : Real.Angle) := by
      exact congr_arg (fun (x : ℝ) => (x : Real.Angle)) hc'
    rw [ha, hb] at h_eq_angle
    exact h_eq_angle
  exact h_inj2 h

/-- **S 的单射性（W1 严格）**：`Function.Injective S`。 -/
theorem actionPhase_injective {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C] :
    Function.Injective (@actionPhase M C _ _) := by
  intro α β h_eq
  have h1' : ‖Cx.amplitude α‖ = 1 := h1 (h := Cx.norm_one α)
  have h2' : ‖Cx.amplitude β‖ = 1 := h1 (h := Cx.norm_one β)
  have hm1 : Cx.amplitude α ∈ Submonoid.unitSphere ℂ := h2 h1'
  have hm2 : Cx.amplitude β ∈ Submonoid.unitSphere ℂ := h2 h2'
  have h1 : Real.Angle.toCircle (@actionPhase M C _ _ α) =
      Real.Angle.toCircle (@actionPhase M C _ _ β) := by rw [h_eq]
  have h2 : (Subtype.mk (Cx.amplitude α) hm1 : Circle) =
      (Subtype.mk (Cx.amplitude β) hm2 : Circle) := by
    have ha : Real.Angle.toCircle (@actionPhase M C _ _ α) =
        Subtype.mk (Cx.amplitude α) hm1 := bridge α
    have hb : Real.Angle.toCircle (@actionPhase M C _ _ β) =
        Subtype.mk (Cx.amplitude β) hm2 := bridge β
    rw [ha, hb] at h1
    exact h1
  have h3 : Cx.amplitude α = Cx.amplitude β := Subtype.ext_iff.mp h2
  exact Cx.amplitude_injective h3

/-- **重构振幅（W1 严格）**：
    `(toCircle (S α) : ℂ) = amplitude α`。 -/
theorem actionPhase_reconstructs_amplitude {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α : C) :
    (Real.Angle.toCircle (@actionPhase M C _ _ α) : ℂ) = Cx.amplitude α := by
  have h_norm : ‖Cx.amplitude α‖ = 1 := h1 (h := Cx.norm_one α)
  have h_mem : Cx.amplitude α ∈ Submonoid.unitSphere ℂ := h2 h_norm
  have h1 : Real.Angle.toCircle (@actionPhase M C _ _ α) =
      Subtype.mk (Cx.amplitude α) h_mem := bridge α
  rw [h1]

end CSQIT_V1Bridge
