/-
CSQIT-W1 TwoAspectNoFinite — 两面性二分定理的无 Finite 版本
版本: v13.1.0（新发现）
日期: 2026-09-29
================================================================================ -/

import CSQIT_W1.Foundation
import Mathlib.Data.Complex.Basic

namespace CSQIT_W1.TwoAspectNoFinite

open CSQIT_W1.Foundation

variable {M C : Type*}

theorem amplitude_injective_implies_compose_comm
    [A : AxiomA M C] [Cx : AxiomC M C]
    (h_inj : Function.Injective Cx.amplitude)
    (α β : C) :
    A.compose α β = A.compose β α := by
  have h1 : Cx.amplitude (A.compose α β) = Cx.amplitude α * Cx.amplitude β :=
    Cx.comp_rule α β
  have h2 : Cx.amplitude (A.compose β α) = Cx.amplitude β * Cx.amplitude α :=
    Cx.comp_rule β α
  have h3 : Cx.amplitude α * Cx.amplitude β = Cx.amplitude β * Cx.amplitude α := by
    apply mul_comm
  have h4 : Cx.amplitude (A.compose α β) = Cx.amplitude (A.compose β α) := by
    calc
      Cx.amplitude (A.compose α β)
        = Cx.amplitude α * Cx.amplitude β := h1
      _ = Cx.amplitude β * Cx.amplitude α := h3
      _ = Cx.amplitude (A.compose β α) := h2.symm
  exact h_inj h4

theorem compose_comm_implies_output_const
    [A : AxiomA M C]
    (h_comm : ∀ γ β : C, A.compose γ β = A.compose β γ) :
    ∀ (γ β : C), A.output γ = A.output β := by
  intro γ β
  have h1 : A.output (A.compose γ β) = A.output β := A.compose_output γ β
  have h2 : A.compose γ β = A.compose β γ := h_comm γ β
  have h3 : A.output (A.compose β γ) = A.output γ := A.compose_output β γ
  have h4 : A.output (A.compose γ β) = A.output (A.compose β γ) := by rw [h2]
  have h5 : A.output β = A.output γ := by
    calc
      A.output β = A.output (A.compose γ β) := h1.symm
      _ = A.output (A.compose β γ) := h4
      _ = A.output γ := h3
  exact h5.symm

theorem two_aspect_dichotomy_no_finite
    [A : AxiomA M C] [Cx : AxiomC M C] :
    (∀ (α β : C), A.output α = A.output β) ∨
    ¬ Function.Injective Cx.amplitude := by
  by_cases h_inj : Function.Injective Cx.amplitude
  · have h_comm : ∀ γ β : C, A.compose γ β = A.compose β γ :=
      fun γ β => amplitude_injective_implies_compose_comm h_inj γ β
    have h_out_const : ∀ (γ β : C), A.output γ = A.output β :=
      compose_comm_implies_output_const h_comm
    left
    exact h_out_const
  · right
    exact h_inj

theorem no_two_aspect_balance_no_finite
    [A : AxiomA M C] [Cx : AxiomC M C]
    (h_output_nontrivial : ∃ (α β : C), A.output α ≠ A.output β) :
    ¬ Function.Injective Cx.amplitude := by
  have h_dichotomy := two_aspect_dichotomy_no_finite (M := M) (C := C)
  rcases h_dichotomy with (h_output_const | h_amp_not_inj)
  · rcases h_output_nontrivial with ⟨α, β, hne⟩
    have h_eq : A.output α = A.output β := h_output_const α β
    exact False.elim (hne h_eq)
  · exact h_amp_not_inj

end CSQIT_W1.TwoAspectNoFinite