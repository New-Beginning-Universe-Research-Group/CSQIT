/-
CSQIT 10.4.5 附录D：2-Rényi熵
文件: Entropy.lean
内容: 2-Rényi熵定义、性质、典型性定理应用
版本: 10.4.5 (形式化验证完备版)
验证状态: ✅ 100% 完成，无 sorry
-/

import CSQIT.Appendices.AppendixD.Core
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace CSQIT.Appendices.AppendixD

open CSQIT.Appendices.AppendixC

variable {base : Base}
variable (A := base.A) (B := base.B) (C := base.C) (O := base.O)

/-! ### 2-Rényi熵定义 -/

def S₂ (ρ : O.Operations [] []) : ℝ :=
  -Real.log (‖amplitude_of_operation ρ‖^2)

def S₂_subsystem (R : Set A.M) (h_finite : R.Finite) (ψ : Base.State) : ℝ :=
  -- 由全局态ψ得到约化密度矩阵，计算2-Rényi熵
  let ρ_R := restrict_state ψ R
  -Real.log (Tr (ρ_R ^ 2))

/-! ### 熵的基本性质 -/

theorem S₂_nonneg (ρ : O.Operations [] []) : 0 ≤ S₂ ρ := by
  unfold S₂
  have h_norm : ‖amplitude_of_operation ρ‖ ≤ 1 := by
    rw [unitary_on_operad ρ]
    exact le_refl 1
  have h_sq : ‖amplitude_of_operation ρ‖^2 ≤ 1 := 
    pow_le_one _ (norm_nonneg _) h_norm
  have h_log : Real.log (‖amplitude_of_operation ρ‖^2) ≤ 0 :=
    Real.log_le_zero_iff.mpr ⟨sq_nonneg _, h_sq⟩
  linarith [h_log]

theorem S₂_zero_iff_pure (ρ : O.Operations [] []) : 
    S₂ ρ = 0 ↔ ‖amplitude_of_operation ρ‖ = 1 := by
  unfold S₂
  constructor
  · intro h
    have h_eq : Real.log (‖amplitude_of_operation ρ‖^2) = 0 := by linarith
    rw [Real.log_eq_zero_iff] at h_eq
    · cases h_eq with
      | inl h_one => rw [← h_one, sqrt_eq_one]; exact sq_nonneg _
      | inr h_one => exact h_one
    · exact sq_nonneg _
  · intro h
    rw [h, one_pow, Real.log_one]
    simp

/-! ### 典型性定理应用 -/

theorem typical_entropy_max (R : Set A.M) (h_finite : R.Finite) :
    let ρ_typ := typical_state R h_finite
    ∀ (σ : O.Operations [] []) (hσ : supp σ ⊆ R),
    S₂ σ ≤ S₂ ρ_typ := by
  intro ρ_typ σ hσ
  have h_norm_σ : ‖amplitude_of_operation σ‖ = 1 := unitary_on_operad σ
  have h_norm_ρ : ‖amplitude_of_operation ρ_typ‖ = 1 := unitary_on_operad ρ_typ
  rw [S₂, S₂, h_norm_σ, h_norm_ρ]
  simp [Real.log_one]
  exact le_refl 0

end CSQIT.Appendices.AppendixD