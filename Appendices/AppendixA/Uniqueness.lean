/-
CSQIT 10.5 附录A：振幅性质与唯一性定理
文件: Appendices/AppendixA/Uniqueness.lean
版本: 10.5 (数学根本优化版)
日期: 2026-06-28
================================================================================
由 AxiomA + AxiomC 推导的振幅基本性质与唯一性定理。
================================================================================
-/

import Core.Axioms
import Core.Theorems
import Mathlib.Data.Complex.Basic

namespace CSQIT.Appendices.AppendixA.Uniqueness

open CSQIT

/-! ============================================================================
   1. 振幅的基本性质
   ============================================================================ -/

/--
定理 A.1: 振幅的幺正性
**证明程度**: ✅ 完整证明
-/
theorem amplitude_norm_one {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α : C) : Complex.normSq (Cx.amplitude α) = 1 :=
  Cx.norm_one α

/--
定理 A.2: 振幅非零性
**证明程度**: ✅ 完整证明
-/
theorem amplitude_ne_zero {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α : C) : Cx.amplitude α ≠ 0 := by
  intro h_zero
  have h_norm : Complex.normSq (Cx.amplitude α) = 1 := Cx.norm_one α
  rw [h_zero] at h_norm
  have h_absurd : (0 : ℝ) = 1 := by
    simpa [Complex.normSq] using h_norm
  exact absurd h_absurd (by norm_num)

/--
定理 A.3: 组合振幅的乘法性
**证明程度**: ✅ 完整证明
-/
theorem amplitude_compose {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α β : C) : Cx.amplitude (A.compose α β) = Cx.amplitude α * Cx.amplitude β :=
  Cx.comp_rule α β

/--
定理 A.4: 振幅结合律一致性
**证明程度**: ✅ 完整证明
-/
theorem amplitude_compose_assoc {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α β γ : C) :
    Cx.amplitude (A.compose (A.compose α β) γ) =
    Cx.amplitude α * (Cx.amplitude β * Cx.amplitude γ) := by
  have h_inner : Cx.amplitude (A.compose α β) = Cx.amplitude α * Cx.amplitude β :=
    Cx.comp_rule α β
  have h_outer : Cx.amplitude (A.compose (A.compose α β) γ) =
      Cx.amplitude (A.compose α β) * Cx.amplitude γ :=
    Cx.comp_rule (A.compose α β) γ
  rw [h_inner] at h_outer
  exact Eq.trans h_outer (by ring)

/-! ============================================================================
   2. 振幅相等蕴含规则相等
   ============================================================================ -/

/--
定理 A.5: 振幅相等蕴含规则相等
**证明程度**: ✅ 完整证明
-/
theorem amplitude_eq_imp_rule_eq {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    {α β : C} (h : Cx.amplitude α = Cx.amplitude β) : α = β :=
  Cx.amplitude_injective h

/-! ============================================================================
   3. 振幅消去律
   ============================================================================ -/

/--
定理 A.6: 振幅左消去律
**证明程度**: ✅ 完整证明
-/
theorem amplitude_left_cancel {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    {α β γ : C}
    (h : Cx.amplitude α * Cx.amplitude γ = Cx.amplitude β * Cx.amplitude γ) :
    Cx.amplitude α = Cx.amplitude β := by
  have h_nonzero : Cx.amplitude γ ≠ 0 := amplitude_ne_zero γ
  have h_comm_left : Cx.amplitude α * Cx.amplitude γ = Cx.amplitude γ * Cx.amplitude α := by ring
  have h_comm_right : Cx.amplitude β * Cx.amplitude γ = Cx.amplitude γ * Cx.amplitude β := by ring
  rw [h_comm_left, h_comm_right] at h
  exact mul_left_cancel₀ h_nonzero h

/--
定理 A.7: 振幅右消去律
**证明程度**: ✅ 完整证明
-/
theorem amplitude_right_cancel {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    {α β γ : C}
    (h : Cx.amplitude α * Cx.amplitude β = Cx.amplitude α * Cx.amplitude γ) :
    Cx.amplitude β = Cx.amplitude γ := by
  have h_nonzero : Cx.amplitude α ≠ 0 := amplitude_ne_zero α
  exact mul_left_cancel₀ h_nonzero h

/-! ============================================================================
   4. 规则左消去律
   ============================================================================ -/

/--
定理 A.8: 规则左消去律
若 α ∘ γ = β ∘ γ，则 α = β
**证明程度**: ✅ 完整证明
-/
theorem compose_left_cancel {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    {α β γ : C} (h : A.compose α γ = A.compose β γ) : α = β := by
  have h₁ : Cx.amplitude (A.compose α γ) = Cx.amplitude (A.compose β γ) := by
    rw [h]
  have h₂ : Cx.amplitude (A.compose α γ) = Cx.amplitude α * Cx.amplitude γ :=
    Cx.comp_rule α γ
  have h₃ : Cx.amplitude (A.compose β γ) = Cx.amplitude β * Cx.amplitude γ :=
    Cx.comp_rule β γ
  have h₄ : Cx.amplitude α * Cx.amplitude γ = Cx.amplitude β * Cx.amplitude γ := by
    rw [←h₂, h₁, h₃]
  have hz : Cx.amplitude γ ≠ 0 := amplitude_ne_zero γ
  have h₅ : Cx.amplitude α = Cx.amplitude β := by
    apply mul_right_cancel₀ hz
    exact h₄
  exact Cx.amplitude_injective h₅

/-! ============================================================================
   5. 规则右消去律
   ============================================================================ -/

/--
定理 A.9: 规则右消去律
若 α ∘ β = α ∘ γ，则 β = γ
**证明程度**: ✅ 完整证明
-/
theorem compose_right_cancel {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    {α β γ : C} (h : A.compose α β = A.compose α γ) : β = γ := by
  have h₁ : Cx.amplitude (A.compose α β) = Cx.amplitude (A.compose α γ) := by
    rw [h]
  have h₂ : Cx.amplitude (A.compose α β) = Cx.amplitude α * Cx.amplitude β :=
    Cx.comp_rule α β
  have h₃ : Cx.amplitude (A.compose α γ) = Cx.amplitude α * Cx.amplitude γ :=
    Cx.comp_rule α γ
  have h₄ : Cx.amplitude α * Cx.amplitude β = Cx.amplitude α * Cx.amplitude γ := by
    rw [←h₂, h₁, h₃]
  have hz : Cx.amplitude α ≠ 0 := amplitude_ne_zero α
  have h₅ : Cx.amplitude β = Cx.amplitude γ := by
    apply mul_left_cancel₀ hz
    exact h₄
  exact Cx.amplitude_injective h₅

/-! ============================================================================
   6. 组合振幅的唯一分解性
   ============================================================================ -/

/--
定理 A.10: 组合振幅的唯一分解性
若 α ∘ β = γ ∘ δ 且 amplitude(α) = amplitude(γ)，则 β = δ
**证明程度**: ✅ 完整证明
-/
theorem unique_factorization {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    {α β γ δ : C}
    (h : A.compose α β = A.compose γ δ)
    (hαγ : Cx.amplitude α = Cx.amplitude γ) : β = δ := by
  have h₁ : Cx.amplitude (A.compose α β) = Cx.amplitude (A.compose γ δ) := by
    rw [h]
  have h₂ : Cx.amplitude (A.compose α β) = Cx.amplitude α * Cx.amplitude β :=
    Cx.comp_rule α β
  have h₃ : Cx.amplitude (A.compose γ δ) = Cx.amplitude γ * Cx.amplitude δ :=
    Cx.comp_rule γ δ
  have h₄ : Cx.amplitude α * Cx.amplitude β = Cx.amplitude γ * Cx.amplitude δ := by
    rw [←h₂, h₁, h₃]
  have h₅ : Cx.amplitude α * Cx.amplitude β = Cx.amplitude α * Cx.amplitude δ := by
    have h₅₁ : Cx.amplitude γ * Cx.amplitude δ = Cx.amplitude α * Cx.amplitude δ := by
      congr 1
      exact hαγ.symm
    have h₅₂ : Cx.amplitude α * Cx.amplitude β = Cx.amplitude α * Cx.amplitude δ := by
      calc
        Cx.amplitude α * Cx.amplitude β
          = Cx.amplitude γ * Cx.amplitude δ := h₄
        _ = Cx.amplitude α * Cx.amplitude δ := h₅₁
    exact h₅₂
  have hz : Cx.amplitude α ≠ 0 := amplitude_ne_zero α
  have h₆ : Cx.amplitude β = Cx.amplitude δ := mul_left_cancel₀ hz h₅
  exact Cx.amplitude_injective h₆

end CSQIT.Appendices.AppendixA.Uniqueness
