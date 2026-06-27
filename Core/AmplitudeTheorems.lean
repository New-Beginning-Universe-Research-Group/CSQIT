import Core.Axioms
import Mathlib.Data.Complex.Basic

namespace CSQIT

set_option linter.unusedVariables false
set_option linter.unusedTactic false

variable {M C : Type*}

/-! ============================================================================
   振幅结构定理（Amplitude Structure Theorems）
   ============================================================================

   本文件包含 CSQIT 理论中关于振幅（amplitude）结构的核心定理。

   核心定理：
   1. amplitude_norm_one — 振幅幺正性
   2. amplitude_compose — 振幅乘法律
   3. amplitude_compose_assoc — 振幅结合律一致性
   4. amplitude_eq_imp_rule_eq — 振幅相等蕴含规则相等（单射性）
   5. amplitude_left_cancel — 振幅左消去律
   6. amplitude_eq_of_compose — 振幅相等的组合判定
   7. amplitude_right_cancel — 振幅右消去律
   ============================================================================ -/

/-! ----------------------------------------------------------------------------
   振幅的基本性质
   ---------------------------------------------------------------------------- -/

/-- 振幅的幺正性 -/
@[simp] theorem amplitude_norm_one [A : AxiomA M C] [Cx : AxiomC M C] (α : C) :
    Complex.normSq (Cx.amplitude α) = 1 :=
  Cx.norm_one α

/-- 组合振幅的乘法性 -/
theorem amplitude_compose [A : AxiomA M C] [Cx : AxiomC M C] (α β : C) :
    Cx.amplitude (A.compose α β) = Cx.amplitude α * Cx.amplitude β :=
  Cx.comp_rule α β

/-- 振幅结合律一致性 -/
theorem amplitude_compose_assoc [A : AxiomA M C] [Cx : AxiomC M C] (α β γ : C) :
    Cx.amplitude (A.compose (A.compose α β) γ) =
    Cx.amplitude α * (Cx.amplitude β * Cx.amplitude γ) := by
  have h1 : Cx.amplitude (A.compose (A.compose α β) γ) =
      Cx.amplitude (A.compose α β) * Cx.amplitude γ :=
    Cx.comp_rule (A.compose α β) γ
  have h2 : Cx.amplitude (A.compose α β) = Cx.amplitude α * Cx.amplitude β :=
    Cx.comp_rule α β
  rw [h1, h2]
  ring

/-- 振幅复合结合律（完整版本） -/
theorem amplitude_assoc_full [A : AxiomA M C] [Cx : AxiomC M C] (α β γ : C) :
    Cx.amplitude (A.compose (A.compose α β) γ) =
    Cx.amplitude α * (Cx.amplitude β * Cx.amplitude γ) :=
  amplitude_compose_assoc α β γ

/-- 振幅相等蕴含规则相等 -/
theorem amplitude_eq_imp_rule_eq [A : AxiomA M C] [Cx : AxiomC M C]
    (α β : C) (h : Cx.amplitude α = Cx.amplitude β) : α = β :=
  Cx.amplitude_injective h

/-! ----------------------------------------------------------------------------
   振幅消去律与组合判定
   ---------------------------------------------------------------------------- -/

/-- 振幅左消去律 -/
theorem amplitude_left_cancel
    {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α β : C) : Cx.amplitude α = Cx.amplitude β → α = β :=
  fun h => Cx.amplitude_injective h

/-- 振幅相等的组合判定：
    若两条规则 `α ∘ β` 与 `α ∘ γ` 的振幅相等，则 `β = γ`。 -/
theorem amplitude_eq_of_compose
    {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α β γ : C) :
    Cx.amplitude (A.compose α β) = Cx.amplitude (A.compose α γ) ↔ β = γ := by
  constructor
  · -- 正向：振幅相等 → β = γ
    intro h
    have h1 : Cx.amplitude (A.compose α β) = Cx.amplitude α * Cx.amplitude β :=
      Cx.comp_rule α β
    have h2 : Cx.amplitude (A.compose α γ) = Cx.amplitude α * Cx.amplitude γ :=
      Cx.comp_rule α γ
    rw [h1, h2] at h
    have hnorm : Complex.normSq (Cx.amplitude α) = 1 := Cx.norm_one α
    have hne : (Cx.amplitude α) ≠ 0 := by
      intro hzero
      have h1 : Complex.normSq (Cx.amplitude α) = 1 := Cx.norm_one α
      rw [hzero] at h1
      simp [Complex.normSq] at h1
    have hmul : (Cx.amplitude α) * (Cx.amplitude β) = (Cx.amplitude α) * (Cx.amplitude γ) := h
    have hcancel : Cx.amplitude β = Cx.amplitude γ := by
      apply mul_left_cancel₀ hne
      exact hmul
    exact Cx.amplitude_injective hcancel
  · -- 反向：β = γ → 振幅相等
    intro h
    rw [h]

/-- 振幅右消去律 -/
theorem amplitude_right_cancel [A : AxiomA M C] [Cx : AxiomC M C]
    (α β γ : C) :
    Cx.amplitude (A.compose α γ) = Cx.amplitude (A.compose β γ) ↔ α = β := by
  constructor
  · -- 正向
    intro h
    have h1 : Cx.amplitude (A.compose α γ) = Cx.amplitude α * Cx.amplitude γ :=
      Cx.comp_rule α γ
    have h2 : Cx.amplitude (A.compose β γ) = Cx.amplitude β * Cx.amplitude γ :=
      Cx.comp_rule β γ
    rw [h1, h2] at h
    have hnorm : Complex.normSq (Cx.amplitude γ) = 1 := Cx.norm_one γ
    have hne : (Cx.amplitude γ) ≠ 0 := by
      intro hzero
      have h1 : Complex.normSq (Cx.amplitude γ) = 1 := Cx.norm_one γ
      rw [hzero] at h1
      simp [Complex.normSq] at h1
    have hmul : (Cx.amplitude α) * (Cx.amplitude γ) = (Cx.amplitude β) * (Cx.amplitude γ) := h
    have hcancel : Cx.amplitude α = Cx.amplitude β := by
      apply mul_right_cancel₀ hne
      exact hmul
    exact Cx.amplitude_injective hcancel
  · -- 反向
    intro h
    rw [h]

/-- 幂等规则的振幅为 1 -/
theorem compose_idempotent_amplitude [A : AxiomA M C] [Cx : AxiomC M C]
    (α : C) (h : A.compose α α = α) : Cx.amplitude α = 1 := by
  have h1 : Cx.amplitude (A.compose α α) = Cx.amplitude α * Cx.amplitude α :=
    Cx.comp_rule α α
  have h2 : Cx.amplitude α * Cx.amplitude α = Cx.amplitude α := by
    rw [h] at h1
    exact h1.symm
  have hnorm : Complex.normSq (Cx.amplitude α) = 1 := Cx.norm_one α
  have hne : (Cx.amplitude α) ≠ 0 := by
    intro hzero
    rw [hzero] at hnorm
    simp [Complex.normSq] at hnorm
  have h3 : Cx.amplitude α * Cx.amplitude α = Cx.amplitude α * 1 := by
    rw [h2] <;> ring
  apply mul_left_cancel₀ hne
  exact h3

/-- 有单位元时振幅为 1 -/
theorem unit_rule_amplitude_one [A : AxiomA M C] [Cx : AxiomC M C]
    (e : C) (h_left : ∀ α, A.compose e α = α) :
    Cx.amplitude e = 1 := by
  have h1 : Cx.amplitude (A.compose e e) = Cx.amplitude e * Cx.amplitude e :=
    Cx.comp_rule e e
  have h2 : A.compose e e = e := h_left e
  have h3 : Cx.amplitude e * Cx.amplitude e = Cx.amplitude e := by
    rw [h2] at h1
    exact h1.symm
  have hnorm : Complex.normSq (Cx.amplitude e) = 1 := Cx.norm_one e
  have hne : (Cx.amplitude e) ≠ 0 := by
    intro hzero
    rw [hzero] at hnorm
    simp [Complex.normSq] at hnorm
  have h4 : Cx.amplitude e * Cx.amplitude e = Cx.amplitude e * 1 := by
    rw [h3] <;> ring
  apply mul_left_cancel₀ hne
  exact h4

end CSQIT
