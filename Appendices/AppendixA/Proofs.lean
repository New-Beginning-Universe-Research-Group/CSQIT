/-
📝 附录A：振幅函数的详细证明
文件: Appendices/AppendixA/Proofs.lean
================================================================================
本文件包含振幅函数基本性质的详细证明推导。
所有定理均是 AxiomA 和 AxiomC 字段的严格推导。
================================================================================
-/

import Core.Axioms
import Mathlib.Data.Complex.Basic

namespace CSQIT.Appendices.AppendixA.Proofs

open CSQIT

/-! ============================================================================
   1. 振幅的幺正性与非零性（详细证明）
   ============================================================================ -/

/--
定理 A.1: 振幅的幺正性（详细证明）
证明策略: 直接应用 AxiomC.norm_one 公理
-/
theorem amplitude_norm_one {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α : C) : Complex.normSq (Cx.amplitude α) = 1 :=
  Cx.norm_one α

/--
定理 A.2: 振幅非零性（详细证明）
证明策略: 
  1. 假设 amplitude α = 0
  2. 由 norm_one 得 |0|² = 1，即 0 = 1
  3. 矛盾，因此 amplitude α ≠ 0
-/
theorem amplitude_ne_zero {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α : C) : Cx.amplitude α ≠ 0 := by
  intro h_zero
  have h_norm : Complex.normSq (Cx.amplitude α) = 1 := Cx.norm_one α
  rw [h_zero] at h_norm
  have h_absurd : (0 : ℝ) = 1 := by
    simp only [Complex.normSq_zero, add_zero] at h_norm
    exact h_norm
  exact absurd h_absurd (by norm_num)

/-! ============================================================================
   2. 组合振幅的乘法性（详细证明）
   ============================================================================ -/

/--
定理 A.3: 组合振幅的乘法性（详细证明）
证明策略: 直接应用 AxiomC.comp_rule 公理
-/
theorem amplitude_compose {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α β : C) : Cx.amplitude (A.compose α β) = Cx.amplitude α * Cx.amplitude β :=
  Cx.comp_rule α β

/--
定理 A.4: 振幅结合律一致性（详细证明）
证明策略:
  1. 对内层组合应用 comp_rule
  2. 对外层组合应用 comp_rule
  3. 应用复数乘法结合律
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
   3. 振幅确定规则（单射性，详细证明）
   ============================================================================ -/

/--
定理 A.5: 振幅相等蕴含规则相等（详细证明）
证明策略: 直接应用 AxiomC.amplitude_injective 公理
-/
theorem amplitude_eq_imp_rule_eq {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    {α β : C} (h : Cx.amplitude α = Cx.amplitude β) : α = β :=
  Cx.amplitude_injective h

/--
定理 A.6: 振幅左消去律（详细证明）
证明策略:
  1. 由 amplitude_ne_zero 得 amplitude γ ≠ 0
  2. 在复数域中，非零元素可消去
  3. 应用 mul_left_cancel₀ 完成证明
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

end CSQIT.Appendices.AppendixA.Proofs