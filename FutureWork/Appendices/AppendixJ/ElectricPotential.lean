/-
================================================================================
CSQIT Future Work - 附录 J：电势差的形成原理
文件: FutureWork/Appendices/AppendixJ/ElectricPotential.lean
版本: v11.2.0
日期: 2026-07-07
状态: 概念框架 / 草稿阶段 ⚠️
================================================================================
-/

import Core.Axioms
import Core.CausalLattice
import Core.TwoAspectTheorems
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace CSQIT.FutureWork.AppendixJ.ElectricPotential

open CSQIT CSQIT.CausalLattice Classical
open Finset BigOperators

set_option linter.unusedVariables false

section ElectricPotentialDefinition

variable {M C : Type*} [CausalLattice M] [A : AxiomA M C] [Cx : AxiomC M C]
variable [Fintype M] [Fintype C] [DecidableEq M]

noncomputable def informationPotential (x : M) : ℝ :=
  let s := Finset.filter (fun α : C => A.output α = x) Finset.univ
  let psi_sq := ∑ α ∈ s, Complex.normSq (Cx.amplitude α)
  - Real.log (psi_sq + 1)

noncomputable def electricPotential (x : M) : ℝ := informationPotential x

noncomputable def potentialDifference (x y : M) : ℝ :=
  electricPotential y - electricPotential x

theorem potentialDifference_antisymm (x y : M) :
    potentialDifference x y = -potentialDifference y x := by
  unfold potentialDifference
  ring

end ElectricPotentialDefinition

section DiscreteElectricField

variable {M C : Type*} [CausalLattice M] [A : AxiomA M C] [Cx : AxiomC M C]
variable [Fintype M] [Fintype C] [DecidableEq M]
variable [LinearOrder M]

def isImmediateSuccessor (x y : M) : Prop :=
  x < y ∧ ¬ ∃ z : M, x < z ∧ z < y

noncomputable def electricFieldAlongEdge (x y : M) : ℝ :=
  if isImmediateSuccessor x y then
    electricPotential x - electricPotential y
  else
    0

noncomputable def electricFieldMagnitude (x : M) : ℝ :=
  let s := Finset.filter (fun y : M => isImmediateSuccessor x y ∨ isImmediateSuccessor y x) Finset.univ
  ∑ y ∈ s, |electricPotential x - electricPotential y|

end DiscreteElectricField

section DiscreteCharge

variable {M C : Type*} [CausalLattice M] [A : AxiomA M C] [Cx : AxiomC M C]
variable [Fintype M] [Fintype C] [DecidableEq M]
variable [LinearOrder M]

noncomputable def discreteDivergence (x : M) : ℝ :=
  let out_s := Finset.filter (fun y : M => isImmediateSuccessor x y) Finset.univ
  let in_s := Finset.filter (fun y : M => isImmediateSuccessor y x) Finset.univ
  (∑ y ∈ out_s, electricFieldAlongEdge x y) -
  (∑ y ∈ in_s, electricFieldAlongEdge y x)

noncomputable def chargeDensity (x : M) : ℝ := discreteDivergence x

end DiscreteCharge

section PotentialFormation

variable {M C : Type*} [CausalLattice M] [A : AxiomA M C] [Cx : AxiomC M C]
variable [Fintype M] [Fintype C] [DecidableEq M]

noncomputable def twoAspectPolarization (S : Set M) : ℝ :=
  let s_finset := S.toFinset
  let n := s_finset.card
  if n = 0 then 0
  else
    let v_bar := (∑ x ∈ s_finset, electricPotential x) / (n : ℝ)
    (∑ x ∈ s_finset, (electricPotential x - v_bar)^2) / (n : ℝ)

theorem potentialDiffIffPolarization (S : Set M) (h_nonempty : Set.Nonempty S) :
    (∃ x ∈ S, ∃ y ∈ S, electricPotential x ≠ electricPotential y) ↔
    twoAspectPolarization S > 0 := by
  let s_finset := S.toFinset
  let v_bar := (∑ x ∈ s_finset, electricPotential x) / (s_finset.card : ℝ)
  have h_nonempty_finset : s_finset.Nonempty := by
    cases h_nonempty with | intro x hx =>
      exact ⟨x, by simp [s_finset, hx]⟩
  have h_n_pos : s_finset.card > 0 := Finset.card_pos.mpr h_nonempty_finset
  have h_denom_pos : (s_finset.card : ℝ) > 0 := by exact_mod_cast h_n_pos
  have h_eq : twoAspectPolarization S =
      (∑ x ∈ s_finset, (electricPotential x - v_bar)^2) / (s_finset.card : ℝ) := by
    unfold twoAspectPolarization
    rw [if_neg (ne_of_gt h_n_pos)]
    <;> rfl
  have h_nonneg : ∀ z ∈ s_finset, 0 ≤ (electricPotential z - v_bar)^2 := by
    intro z _
    exact sq_nonneg _
  have h_sum_nonneg : 0 ≤ ∑ z ∈ s_finset, (electricPotential z - v_bar)^2 := by
    apply Finset.sum_nonneg
    exact h_nonneg
  have h_main : (∃ x ∈ s_finset, ∃ y ∈ s_finset, electricPotential x ≠ electricPotential y) →
      (∑ z ∈ s_finset, (electricPotential z - v_bar)^2) > 0 := by
    intro h_diff
    rcases h_diff with ⟨x, hx, y, hy, h_xy⟩
    by_contra h_not_pos
    have h_sum_zero : ∑ z ∈ s_finset, (electricPotential z - v_bar)^2 = 0 := by linarith
    have h_all_zero : ∀ z ∈ s_finset, (electricPotential z - v_bar)^2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h_sum_zero
    have hx_eq : electricPotential x = v_bar := by
      have h1 : (electricPotential x - v_bar)^2 = 0 := h_all_zero x hx
      have h2 : electricPotential x - v_bar = 0 := by simpa [sq_eq_zero_iff] using h1
      linarith
    have hy_eq : electricPotential y = v_bar := by
      have h1 : (electricPotential y - v_bar)^2 = 0 := h_all_zero y hy
      have h2 : electricPotential y - v_bar = 0 := by simpa [sq_eq_zero_iff] using h1
      linarith
    have h_contra : electricPotential x = electricPotential y := by
      rw [hx_eq, hy_eq]
    exact h_xy h_contra
  have h_transfer : (∃ x ∈ S, ∃ y ∈ S, electricPotential x ≠ electricPotential y) ↔
      (∃ x ∈ s_finset, ∃ y ∈ s_finset, electricPotential x ≠ electricPotential y) := by
    constructor
    · rintro ⟨x, hx, y, hy, hxy⟩
      exact ⟨x, by simp [s_finset, hx], y, by simp [s_finset, hy], hxy⟩
    · rintro ⟨x, hx, y, hy, hxy⟩
      exact ⟨x, by simpa [s_finset] using hx, y, by simpa [s_finset] using hy, hxy⟩
  rw [h_transfer]
  rw [h_eq]
  constructor
  · exact h_main
  · intro h_sum_pos
    have h : (∑ z ∈ s_finset, (electricPotential z - v_bar)^2) > 0 := h_sum_pos
    by_contra h_all_eq
    have h_const : ∀ x ∈ s_finset, ∀ y ∈ s_finset, electricPotential x = electricPotential y := by
      intro x hx y hy
      simpa [not_exists, not_and] using h_all_eq x hx y hy
    have h_const' : ∃ c : ℝ, ∀ x ∈ s_finset, electricPotential x = c := by
      cases h_nonempty_finset with | intro x₀ hx₀ =>
        refine ⟨electricPotential x₀, fun y hy => ?_⟩
        exact h_const y hy x₀ hx₀
    rcases h_const' with ⟨c, hc⟩
    have h_vbar : v_bar = c := by
      have h_sum : ∑ x ∈ s_finset, electricPotential x = (s_finset.card : ℝ) * c := by
        rw [Finset.sum_congr rfl (fun x hx => hc x hx)]
        simp [Finset.sum_const]
        <;> ring
      dsimp only [v_bar]
      rw [h_sum]
      field_simp
      <;> ring
    have h_sum_zero : ∑ x ∈ s_finset, (electricPotential x - v_bar)^2 = 0 := by
      have h : ∀ x ∈ s_finset, (electricPotential x - v_bar)^2 = 0 := by
        intro x hx
        have h1 : electricPotential x = c := hc x hx
        rw [h1, h_vbar]
        <;> ring
      rw [Finset.sum_congr rfl h]
      <;> simp
    linarith

end PotentialFormation

section EM_Correspondence

end EM_Correspondence

end CSQIT.FutureWork.AppendixJ.ElectricPotential
