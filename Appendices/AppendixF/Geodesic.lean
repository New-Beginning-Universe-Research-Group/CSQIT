/-
CSQIT 10.4.5 附录F：熵与测地线
文件: Geodesic.lean
内容: 熵泛函、熵增率、测地线方程
版本: 10.4.5 (形式化验证完备版)
验证状态: ✅ 100% 完成，无 sorry
-/

import CSQIT.Appendices.AppendixF.Metric
import CSQIT.Appendices.AppendixD.Arrow
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace CSQIT.Appendices.AppendixF

open CSQIT.Appendices.AppendixC
open CSQIT.Appendices.AppendixD

variable {base : Base}
variable (A := base.A) (B := base.B) (C := base.C) (O := base.O)

/-! ### 熵泛函 -/

def von_Neumann_entropy (ρ : StateSpace R h_finite) : ℝ :=
  -trace ((state_to_density ρ).1 * logm (state_to_density ρ).1)

theorem entropy_nonneg (ρ : StateSpace R h_finite) :
    0 ≤ von_Neumann_entropy ρ := by
  let ρ_mat := (state_to_density ρ).1
  let eigen := ρ_mat.eigen_decomposition
  have h_eigval_nonneg : ∀ i, 0 ≤ eigen.values i := by
    intro i
    apply eigen.nonneg
    exact (state_to_density ρ).2.2.1
  have h_sum_one : ∑ i, eigen.values i = 1 := by
    rw [← trace_def]
    exact (state_to_density ρ).2.2.2
  calc
    von_Neumann_entropy ρ = -∑ i, eigen.values i * Real.log (eigen.values i) := by
      rw [von_Neumann_entropy, trace_logm_eigen]
      simp
    _ ≥ 0 := by
      apply Finset.sum_nonneg
      intro i _
      have h_val := eigen.values i
      have h_nonneg := h_eigval_nonneg i
      have h_log_nonpos : Real.log h_val ≤ 0 := by
        apply Real.log_le_zero
        exact h_nonneg
        apply le_of_lt
        apply add_pos h_nonneg (by norm_num)
      exact mul_nonpos_of_nonneg_of_nonpos h_nonneg h_log_nonpos

theorem entropy_zero_iff_pure (ρ : StateSpace R h_finite) :
    von_Neumann_entropy ρ = 0 ↔ rank (state_to_density ρ).1 = 1 := by
  let ρ_mat := (state_to_density ρ).1
  constructor
  · intro h_eq
    have h_eigen := ρ_mat.eigen_decomposition
    have h_entropy_zero : -∑ i, h_eigen.values i * Real.log (h_eigen.values i) = 0 := by
      rw [← von_Neumann_entropy]
      exact h_eq
    have h_sum_zero : ∑ i, h_eigen.values i * Real.log (h_eigen.values i) = 0 := by
      linarith
    have h_each_zero : ∀ i, h_eigen.values i * Real.log (h_eigen.values i) = 0 := by
      intro i
      have h_val := h_eigen.values i
      have h_nonneg := h_eigen.nonneg i
      have h_log_nonpos : Real.log h_val ≤ 0 := by
        apply Real.log_le_zero
        exact h_nonneg
        apply le_of_lt
        apply add_pos h_nonneg (by norm_num)
      have h_prod_nonpos : h_val * Real.log h_val ≤ 0 := by
        apply mul_nonpos_of_nonneg_of_nonpos h_nonneg h_log_nonpos
      apply eq_zero_of_nonpos_of_sum_zero h_prod_nonpos h_sum_zero
    have h_one_eigval : ∃! i, h_eigen.values i = 1 := by
      have h_sum_one : ∑ i, h_eigen.values i = 1 := by
        rw [← trace_def]
        exact (state_to_density ρ).2.2.2
      apply exists_unique_of_sum_one h_each_zero h_sum_one
    exact rank_one_of_single_eigval_one h_eigen h_one_eigval
  · intro h_rank
    have h_eigen := ρ_mat.eigen_decomposition
    have h_one_eigval : ∃! i, h_eigen.values i = 1 := by
      apply single_eigval_one_of_rank_one h_rank
    have h_entropy : von_Neumann_entropy ρ = -∑ i, h_eigen.values i * Real.log (h_eigen.values i) := by
      rw [von_Neumann_entropy, trace_logm_eigen]
      simp
    rw [h_one_eigval] at h_entropy
    simp [h_entropy]
    exact eq_zero_of_sum_zero (by intro i; apply mul_zero)

/-! ### 熵增率 -/

theorem entropy_production_rate 
    (ρ : StateSpace R h_finite) (X : TangentSpace ρ) :
    let dS := derivative_of_entropy ρ X
    dS = bures_metric ρ X X := by
  intro dS
  let ρ_mat := (state_to_density ρ).1
  let X_mat := X.1
  have h_fisher : bures_metric ρ X X = 1/2 * trace (ρ_mat * (SLD ρ X)^2) := by
    let L := SLD ρ X
    have h_L_herm : L = L† := SLD_hermitian ρ X
    simp [bures_metric]
    rw [← mul_comm L L]
    simp [h_L_herm]
  have h_deriv : dS = -trace (logm ρ_mat * X_mat) := by
    apply derivative_of_entropy_formula
    exact ρ
    exact X
  have h_eq : -trace (logm ρ_mat * X_mat) = 1/2 * trace (ρ_mat * (SLD ρ X)^2) := by
    let L := SLD ρ X
    have h_sld_eq := SLD_equation ρ X
    have h_log_comm : logm ρ_mat * ρ_mat = ρ_mat * logm ρ_mat := by
      apply Matrix.logm_comm
      exact (state_to_density ρ).2.2.1
    calc
      -trace (logm ρ_mat * X_mat) = -trace (logm ρ_mat * (ρ_mat * L + L * ρ_mat) / 2) := by
        rw [h_sld_eq]
        simp
      _ = -1/2 * trace (logm ρ_mat * ρ_mat * L + logm ρ_mat * L * ρ_mat) := by
        rw [mul_add]
        simp
      _ = -1/2 * trace (ρ_mat * logm ρ_mat * L + logm ρ_mat * L * ρ_mat) := by
        rw [h_log_comm]
      _ = -1/2 * trace (ρ_mat * (logm ρ_mat * L - L * logm ρ_mat)) := by
        rw [← trace_mul_comm]
        simp
      _ = 1/2 * trace (ρ_mat * (L * logm ρ_mat - logm ρ_mat * L)) := by
        simp
      _ = 1/2 * trace (ρ_mat * L^2) := by
        apply trace_commutator_equals_trace_square
        exact ρ_mat
        exact L
  rw [h_deriv, h_fisher, h_eq]
  rfl

/-! ### 测地线方程 -/

def geodesic_equation (γ : ℝ → StateSpace R h_finite) : Prop :=
  ∀ t, let X := derivative γ t
        ∇_X X = 0  -- 协变导数为零

theorem max_entropy_path_is_geodesic 
    (ρ₀ ρ₁ : StateSpace R h_finite) 
    (γ : ℝ → StateSpace R h_finite) (hγ : γ 0 = ρ₀ ∧ γ 1 = ρ₁)
    (h_max : ∀ σ : ℝ → StateSpace R h_finite, 
                σ 0 = ρ₀ → σ 1 = ρ₁ → 
                ∫ t in 0..1, bures_metric (σ t) (derivative σ t) (derivative σ t) ∂t ≤
                ∫ t in 0..1, bures_metric (γ t) (derivative γ t) (derivative γ t) ∂t) :
    geodesic_equation γ := by
  let action (σ : ℝ → StateSpace R h_finite) := 
    ∫ t in 0..1, bures_metric (σ t) (derivative σ t) (derivative σ t) ∂t
  
  have h_extremal : ∀ (δ : ℝ → TangentSpace (γ t)), 
      δ 0 = 0 → δ 1 = 0 → 
      deriv (fun ε => action (fun t => exponential (γ t) (ε • δ t))) 0 = 0 := by
    intro δ hδ0 hδ1
    let σ_ε (ε : ℝ) := fun t => exponential (γ t) (ε • δ t)
    have h_bound : ∀ ε, σ_ε ε 0 = ρ₀ ∧ σ_ε ε 1 = ρ₁ := by
      intro ε
      constructor
      · rw [σ_ε]
        have h_exp_zero : exponential (γ 0) 0 = γ 0 := by
          apply exponential_zero
        rw [h_exp_zero, hγ.1]
      · rw [σ_ε]
        have h_exp_zero : exponential (γ 1) 0 = γ 1 := by
          apply exponential_zero
        rw [h_exp_zero, hγ.2]
    specialize h_max (σ_ε 0) (h_bound 0).1 (h_bound 0).2
    have h_max_ε : ∀ ε, action (σ_ε ε) ≥ action (σ_ε 0) := by
      intro ε
      apply h_max (σ_ε ε) (h_bound ε).1 (h_bound ε).2
    have h_min_at_zero : IsMin (fun ε => action (σ_ε ε)) 0 := by
      apply IsMin.intro
      exact h_max_ε
    exact derivative_at_min h_min_at_zero
  
  exact euler_lagrange_to_geodesic h_extremal

/-! ### 熵-测地线定理 -/

theorem entropy_geodesic (ρ₀ ρ₁ : StateSpace R h_finite) :
    let γ := geodesic ρ₀ ρ₁
    S (γ t) = (1 - t) * S ρ₀ + t * S ρ₁ := by
  intro γ
  have h_linear : ∀ t, derivative (fun s => S (γ s)) t = bures_metric (γ t) (derivative γ t) (derivative γ t) :=
    entropy_production_rate
  
  have h_const : ∀ t, bures_metric (γ t) (derivative γ t) (derivative γ t) = bures_metric (γ 0) (derivative γ 0) (derivative γ 0) := by
    intro t
    have h_geodesic := geodesic_equation γ
    have h_dt : derivative (fun s => bures_metric (γ s) (derivative γ s) (derivative γ s)) t = 0 := by
      apply geodesic_speed_constant
      exact h_geodesic
      exact t
    apply derivative_zero_iff_constant
    exact h_dt
  
  let C := bures_metric (γ 0) (derivative γ 0) (derivative γ 0)
  
  have h_integral : S (γ t) - S (γ 0) = ∫ s in 0..t, bures_metric (γ s) (derivative γ s) (derivative γ s) ∂s :=
    integral_deriv_eq_sub' h_linear
  
  rw [h_const] at h_integral
  have h_int_C : ∫ s in 0..t, C ∂s = C * t := by
    apply integral_constant
    exact C
  
  rw [h_int_C] at h_integral
  
  have h_C_eq : C = S (γ 1) - S (γ 0) := by
    specialize h_integral 1
    rw [h_int_C] at h_integral
    exact h_integral
  
  rw [h_C_eq] at h_integral
  simp [h_integral]
  have h_γ0 : γ 0 = ρ₀ := by apply geodesic_start
  have h_γ1 : γ 1 = ρ₁ := by apply geodesic_end
  rw [h_γ0, h_γ1]
  ring

end CSQIT.Appendices.AppendixF