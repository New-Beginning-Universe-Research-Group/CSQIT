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
  let s := {α : C | A.output α = x}.toFinset
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
variable [DecidableRel (α := M) (· < ·)]

def isImmediateSuccessor (x y : M) : Prop :=
  x < y ∧ ¬ ∃ z : M, x < z ∧ z < y

noncomputable def electricFieldAlongEdge (x y : M) : ℝ :=
  if isImmediateSuccessor x y then
    electricPotential x - electricPotential y
  else
    0

noncomputable def electricFieldMagnitude (x : M) : ℝ :=
  let s := {y : M | isImmediateSuccessor x y ∨ isImmediateSuccessor y x}
  ∑ y ∈ s.toFinset, |electricPotential x - electricPotential y|

theorem discreteConservativeField {n : ℕ} (path : Vector M (n + 1))
    (h_valid : ∀ i < n, isImmediateSuccessor path[i] path[i+1])
    (h_closed : path[0] = path[n]) :
    ∑ i ∈ range n, (electricPotential path[i+1] - electricPotential path[i]) = 0 := by
  have telescope_sum : ∑ i ∈ range n, (electricPotential path[i+1] - electricPotential path[i]) =
      electricPotential path[n] - electricPotential path[0] := by
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [sum_range_succ]
      rw [ih]
      ring_nf
  rw [telescope_sum]
  rw [h_closed]
  simp

end DiscreteElectricField

section DiscreteCharge

variable {M C : Type*} [CausalLattice M] [A : AxiomA M C] [Cx : AxiomC M C]
variable [Fintype M] [Fintype C] [DecidableEq M]
variable [DecidableRel (α := M) (· < ·)]

noncomputable def discreteDivergence (x : M) : ℝ :=
  let out_s := {y : M | isImmediateSuccessor x y}
  let in_s := {y : M | isImmediateSuccessor y x}
  (∑ y ∈ out_s.toFinset, electricFieldAlongEdge x y) -
  (∑ y ∈ in_s.toFinset, electricFieldAlongEdge y x)

noncomputable def chargeDensity (x : M) : ℝ := discreteDivergence x

theorem discreteGaussTheorem :
    ∑ x : M, chargeDensity x = 0 := by
  unfold chargeDensity discreteDivergence
  rw [sum_sub_distrib]
  have h1 : ∀ x y : M, isImmediateSuccessor x y →
      electricFieldAlongEdge x y = electricPotential x - electricPotential y := by
    intro x y h
    unfold electricFieldAlongEdge
    rw [if_pos h]
  have h2 : ∀ x y : M, isImmediateSuccessor x y →
      electricFieldAlongEdge y x = 0 := by
    intro x y hxy
    have hyx : ¬isImmediateSuccessor y x := by
      intro hyx
      have h1 := hxy.left
      have h2 := hyx.left
      have h3 := h1.trans h2
      exact (lt_irrefl x) h3
    unfold electricFieldAlongEdge
    rw [if_neg hyx]
  let edges := Finset.univ.filter (fun p : M × M => isImmediateSuccessor p.1 p.2)
  have h3 : ∑ x, ∑ y ∈ ({y | isImmediateSuccessor x y}).toFinset,
      electricFieldAlongEdge x y =
      ∑ p ∈ edges, (electricPotential p.1 - electricPotential p.2) := by
    apply Finset.sum_comm
    simp
    intro p hp
    cases p with | mk x y =>
      rw [h1 x y hp]
  have h4 : ∑ x, ∑ y ∈ ({y | isImmediateSuccessor y x}).toFinset,
      electricFieldAlongEdge y x =
      ∑ p ∈ edges, (electricPotential p.1 - electricPotential p.2) := by
    apply Finset.sum_comm
    simp
    intro p hp
    cases p with | mk x y =>
      rw [h2 x y hp]
      simp
  rw [h3, h4]
  ring

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
  have h_nonempty_finset : s_finset.Nonempty := by
    cases h_nonempty with | intro x hx =>
      exact ⟨x, by simp [s_finset, hx]⟩
  have h_n_pos : s_finset.card > 0 := Finset.card_pos.mpr h_nonempty_finset
  have h_eq : twoAspectPolarization S =
      (∑ x ∈ s_finset, (electricPotential x -
        ((∑ y ∈ s_finset, electricPotential y) / (s_finset.card : ℝ)))^2) / (s_finset.card : ℝ) := by
    unfold twoAspectPolarization
    rw [if_neg (ne_of_gt h_n_pos)]
  rw [h_eq]
  let v_bar := (∑ x ∈ s_finset, electricPotential x) / (s_finset.card : ℝ)
  constructor
  · -- mp: 存在电势差 → 极化度 > 0
    intro h_diff
    cases h_diff with | intro x hx =>
      cases hx.right with | intro y hy =>
        have h_xy : electricPotential x ≠ electricPotential y := hy
        have hx' : x ∈ s_finset := by simp [s_finset]; exact hx.left
        have hy' : y ∈ s_finset := by simp [s_finset]; exact hy.left
        have h_pos : (electricPotential x - v_bar)^2 + (electricPotential y - v_bar)^2 > 0 := by
          by_contra h_zero
          have h1 : (electricPotential x - v_bar)^2 = 0 := by
            apply le_antisymm
            · apply sq_nonneg
            · nlinarith
          have h2 : (electricPotential y - v_bar)^2 = 0 := by
            apply le_antisymm
            · apply sq_nonneg
            · nlinarith
          rw [sq_eq_zero_iff] at h1 h2
          rw [h1, h2] at h_xy
          exact h_xy (rfl)
        have h_total : ∑ z ∈ s_finset, (electricPotential z - v_bar)^2 ≥
            (electricPotential x - v_bar)^2 + (electricPotential y - v_bar)^2 := by
          have h1 : (electricPotential x - v_bar)^2 + (electricPotential y - v_bar)^2 =
                    ∑ z ∈ ({x, y} : Finset M), (electricPotential z - v_bar)^2 := by
            simp [hx', hy']
            <;> ring
          rw [h1]
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro z hz
            simp at hz
            cases hz with
            | inl h => rw [h]; exact hx'
            | inr h => rw [h]; exact hy'
          · intro z hz
            apply sq_nonneg
        have h_numerator_pos : ∑ z ∈ s_finset, (electricPotential z - v_bar)^2 > 0 := by
          nlinarith [h_pos, h_total, sq_nonneg (electricPotential x - v_bar),
                     sq_nonneg (electricPotential y - v_bar)]
        have h_denom_pos : (s_finset.card : ℝ) > 0 := by exact_mod_cast h_n_pos
        exact div_pos h_numerator_pos h_denom_pos
  · -- mpr: 极化度 > 0 → 存在电势差
    intro h_polar
    by_contra h_all_eq
    push_neg at h_all_eq
    have h_const : ∃ c : ℝ, ∀ x ∈ s_finset, electricPotential x = c := by
      cases h_nonempty_finset with | intro x₀ hx₀ =>
        use electricPotential x₀
        intro y hy
        have hy' : y ∈ S := by simp [s_finset] at hy; exact hy
        have hx₀' : x₀ ∈ S := by simp [s_finset] at hx₀; exact hx₀
        exact h_all_eq y hy' x₀ hx₀'
    cases h_const with | intro c hc =>
      have h_vbar : v_bar = c := by
        simp [v_bar, hc, Finset.sum_const]
        field_simp
        <;> ring
      have h_sum_zero : ∑ x ∈ s_finset, (electricPotential x - v_bar)^2 = 0 := by
        rw [hc, h_vbar]
        simp
      have h_polar_zero : (∑ x ∈ s_finset, (electricPotential x - v_bar)^2) / (s_finset.card : ℝ) = 0 := by
        rw [h_sum_zero]
        simp
      linarith

end PotentialFormation

section EM_Correspondence

end EM_Correspondence

end CSQIT.FutureWork.AppendixJ.ElectricPotential
