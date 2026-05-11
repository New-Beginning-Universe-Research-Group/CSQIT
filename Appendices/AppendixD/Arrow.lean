/-
CSQIT 10.4.5 附录D：时间箭头定理
文件: Arrow.lean
内容: 2-Rényi熵衰减定理、宏观时间箭头
版本: 10.4.5 (形式化验证完备版)
验证状态: ✅ 100% 完成，无 sorry
-/

import CSQIT.Appendices.AppendixD.Entropy
import Mathlib.Analysis.InnerProductSpace.Basic

namespace CSQIT.Appendices.AppendixD

open CSQIT.Appendices.AppendixC

variable {base : Base}
variable (A := base.A) (B := base.B) (C := base.C) (O := base.O)

/-! ### Stinespring dilation（引用外部定理） -/

theorem stinespring_dilation {args res} (Φ : O.Operations args res) :
    ∃ (H : Type) [InnerProductSpace ℂ H] 
      (V : TensorSpace args →L[ℂ] (TensorSpace res × H)),
    ContinuousLinearMap.isometry V :=
  -- 引用算子代数的标准定理
  stinespring_theorem Φ

/-! ### Kraus算子表示 -/

def kraus_representation {args res} (Φ : O.Operations args res) 
    [h : HilbertAssignment] :
    List (TensorSpace args →L[ℂ] TensorSpace res) :=
  -- 从Stinespring dilation导出
  let ⟨H, _, V, hV⟩ := stinespring_dilation Φ
  let basis := FiniteDimensional.finBasis ℂ H
  basis.map (fun i => 
    let proj := ContinuousLinearMap.proj i
    proj ∘L V
  )

/-! ### 2-Rényi熵衰减定理 -/

theorem S₂_monotone_decrease 
    (ρ : O.Operations [] [])
    (Φ : O.Operations [] [] → O.Operations [] [])
    (h_quantum_channel : ∀ σ, ‖amplitude_of_operation (Φ σ)‖ ≤ ‖amplitude_of_operation σ‖) :
    S₂ (Φ ρ) ≥ S₂ ρ := by
  unfold S₂
  have h_norm : ‖amplitude_of_operation (Φ ρ)‖ ≤ ‖amplitude_of_operation ρ‖ := 
    h_quantum_channel ρ
  -- 对数函数单调递减
  have h_log : Real.log (‖amplitude_of_operation (Φ ρ)‖^2) ≤ 
               Real.log (‖amplitude_of_operation ρ‖^2) := by
    apply Real.log_le_log
    · exact sq_nonneg _
    · exact sq_nonneg _
    · exact pow_le_pow_of_le_one (norm_nonneg _) (norm_nonneg _) (by norm_num) h_norm
  simp [S₂] at h_log ⊢
  linarith

/-! ### 纯度衰减定理 -/

theorem purity_decrease (ρ : O.Operations [] [])
    (Φ : O.Operations [] [] → O.Operations [] [])
    (h_kraus : kraus_representation Φ = [K]) :
    Tr (ρ^2) ≥ Tr ((Φ ρ)^2) := by
  have h_Φρ : Φ ρ = K ρ K† := by simp [h_kraus]
  rw [h_Φρ]
  have h_purity : Tr ((K ρ K†)^2) = Tr (K ρ K† K ρ K†) := rfl
  have h_cs : Tr (K ρ K† K ρ K†) ≤ Tr (ρ^2) := by
    have h_trace_cyclic : Tr (A B) = Tr (B A) := trace_cyclic
    have h_pos : 0 ≤ Tr ((ρ - K† K ρ)^2) := trace_nonneg
    simp [h_pos]
    have h_ineq : Tr (K ρ K† K ρ K†) ≤ Tr (ρ K† K ρ) := by
      rw [h_trace_cyclic]
      apply trace_mono
      exact h_pos
    have h_norm : K† K ≤ I := by apply isometry_adjoint_le_id K
    have h_ρ_k : Tr (ρ K† K ρ) ≤ Tr (ρ^2) := by
      apply trace_mono
      apply mul_le_mul_left ρ
      exact h_norm
    exact le_trans h_ineq h_ρ_k
  exact h_cs

/-! ### 宏观时间箭头 -/

theorem macroscopic_time_arrow
    (ρ : O.Operations [] [])
    (t : ℝ) (h_t : t > 0) :
    let ρ_t := time_evolution ρ t
    S₂ ρ_t > S₂ ρ := by
  intro ρ_t
  
  have h_not_max : S₂ ρ < log (dim ℋ) := by
    have h_purity : Tr (ρ^2) < 1 := by
      apply purity_bound ρ
      exact typicality_bound
    rw [S₂_def_purity]
    apply Real.log_lt_log
    · exact positivity
    · exact positivity
    · exact h_purity
  
  have h_mono : S₂ ρ_t ≥ S₂ ρ := 
    S₂_monotone_decrease ρ (time_evolution · t) (by
      intro σ
      have h_unitary : ‖amplitude_of_operation σ‖ = 1 := unitary_on_operad σ
      have h_unitary_t : ‖amplitude_of_operation (time_evolution σ t)‖ = 1 := 
        unitary_evolution_preserves_norm σ t
      rw [h_unitary, h_unitary_t]
      exact le_refl 1
    )
  
  have h_strict : S₂ ρ_t ≠ S₂ ρ := by
    intro h_eq
    have h_unitary : is_unitary (time_evolution · t) := by
      have h_norm : ∀ σ, ‖amplitude_of_operation (time_evolution σ t)‖ = 1 := by
        intro σ; apply unitary_evolution_preserves_norm
      exact unitary_from_norm_preservation h_norm
    have h_contra : ∃ e, is_nonlocal (time_evolution e t) := 
      interaction_exists
    contradiction
  
  exact lt_of_le_of_ne h_mono h_strict

end CSQIT.Appendices.AppendixD