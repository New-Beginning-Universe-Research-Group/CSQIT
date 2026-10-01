/-
================================================================================
CSQIT-W1 TwoAspect — 一体两面性定理（main 分支精华）
模块: CSQIT_W1.TwoAspect
版本: v13.0.0（统一系统，精简版，零 sorry）
来源: CSQIT main/Core/W1/TwoAspectTheorems.lean
原始日期: 2026-06-28
================================================================================

本模块包含 CSQIT 理论中最深刻的结构性二分定理。

核心发现：
  在满足 AxiomA + AxiomC 的有限模型中，
  以下两者必居其一：
    (a) output 是常函数（因果面退化）
    (b) amplitude 不是单射的（信息面退化）

  等价地说：不存在两面平衡态。

关键 theorem 链：
  amplitude 单射
    ⇒ 左乘映射单射  (amplitude_injective_implies_left_mul_injective)
    ⇒ 左乘映射双射（有限性：单射自映射 ⇒ 满射）
    ⇒ 左可迁性     (amplitude_injective_implies_left_transitive)
    ⇒ output 退化  (output_degenerate_theorem)

物理意义：
  这是"此起彼伏原理"的精确数学形式——
  在标准 CSQIT 框架中，因果面和信息面是"竞争"关系，
  一面的非平凡性以另一面的退化为代价。

统一系统位置：模块 3 / 9
依赖：CSQIT_W1.Foundation（提供 AxiomA + AxiomC）
      Mathlib.Data.Complex.Basic
      Mathlib.Data.Set.Finite.Basic
================================================================================ -/

import CSQIT_W1.Foundation
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Finite.Basic

namespace CSQIT_W1.TwoAspect

open CSQIT_W1.Foundation

variable {M C : Type*}

/-! ============================================================================
   §1. 左可迁性定义（只需 AxiomA）
   ============================================================================

   左可迁性：对任意目标 γ 和"锚点" β，存在 α 使得 compose α β = γ。
   这意味着 (C, compose) 作为二元运算，对固定的 β 左乘是满射。
   ============================================================================ -/

/-- **左可迁性**（定义，只需要 AxiomA）。
    (C, compose) 是左可迁的：对任意 γ, β，存在 α 使得 compose α β = γ。 -/
def left_transitive {M C : Type*} [A : AxiomA M C] : Prop :=
  ∀ (γ β : C), ∃ (α : C), A.compose α β = γ

/-! ============================================================================
   §2. output 退化定理（只需 AxiomA + left_transitive）
   ============================================================================

   核心思想：
     若左可迁性成立，则对任意 γ, β：
       ∃ α, compose α β = γ
       ⇒ output(compose α β) = output γ
       ⇒ output β = output γ    （compose_output 公理）
     因此 output 是常函数。
   ============================================================================ -/

/-- **output 退化定理**（W1 严格，只需要 AxiomA）。
    若左可迁性成立，则 output 退化为常函数。 -/
theorem output_degenerate_theorem [A : AxiomA M C]
    (h : left_transitive (M := M) (C := C)) :
    ∀ (γ β : C), A.output γ = A.output β := by
  intro γ β
  have h₁ : ∃ (α : C), A.compose α β = γ := h γ β
  rcases h₁ with ⟨α, hα⟩
  have h₂ : A.output (A.compose α β) = A.output γ := by rw [hα]
  have h₃ : A.output (A.compose α β) = A.output β := A.compose_output α β
  rw [h₃] at h₂
  exact h₂.symm

/-! ============================================================================
   §3. 振幅单射 ⇒ 左乘单射（只需 AxiomA + AxiomC）
   ============================================================================

   核心思想：
     假设 amplitude 单射，且 compose α₁ β = compose α₂ β。
     则 amplitude(compose α₁ β) = amplitude(compose α₂ β)
     由 comp_rule：amplitude α₁ * amplitude β = amplitude α₂ * amplitude β
     由于 |amplitude β|² = 1，amplitude β ≠ 0，消去得 amplitude α₁ = amplitude α₂
     由单射性，α₁ = α₂。
   ============================================================================ -/

/-- **振幅单射 ⇒ 左乘单射**（W1 严格，AxiomA + AxiomC）。
    若 amplitude 是单射的，则左乘映射 L_β(α) := compose α β 也是单射的。 -/
theorem amplitude_injective_implies_left_mul_injective
    [A : AxiomA M C] [Cx : AxiomC M C]
    (h_inj : Function.Injective Cx.amplitude)
    (β : C) :
    Function.Injective (fun (α : C) => A.compose α β) := by
  intro α₁ α₂ h
  have h_eq : A.compose α₁ β = A.compose α₂ β := by simpa using h
  have h1 : Cx.amplitude (A.compose α₁ β) = Cx.amplitude (A.compose α₂ β) := by
    rw [h_eq]
  have h2 : Cx.amplitude α₁ * Cx.amplitude β = Cx.amplitude α₂ * Cx.amplitude β := by
    have h3 : Cx.amplitude (A.compose α₁ β) = Cx.amplitude α₁ * Cx.amplitude β := Cx.comp_rule α₁ β
    have h4 : Cx.amplitude (A.compose α₂ β) = Cx.amplitude α₂ * Cx.amplitude β := Cx.comp_rule α₂ β
    rw [h3, h4] at h1
    exact h1
  have h_norm_one : (Cx.amplitude β) ≠ 0 := by
    have h5 : Complex.normSq (Cx.amplitude β) = 1 := Cx.norm_one β
    intro h6
    rw [h6] at h5
    simp [Complex.normSq] at h5 <;> norm_num at h5
  have h7 : Cx.amplitude α₁ = Cx.amplitude α₂ := by
    have h9 : Cx.amplitude β ≠ 0 := h_norm_one
    have h11 : (Cx.amplitude α₁ - Cx.amplitude α₂) * Cx.amplitude β = 0 := by
      calc
        (Cx.amplitude α₁ - Cx.amplitude α₂) * Cx.amplitude β
          = Cx.amplitude α₁ * Cx.amplitude β - Cx.amplitude α₂ * Cx.amplitude β := by ring
        _ = 0 := by rw [h2] <;> ring
    have h12 : Cx.amplitude α₁ - Cx.amplitude α₂ = 0 := by
      apply (mul_eq_zero.mp h11).resolve_right h9
    simpa [sub_eq_zero] using h12
  exact h_inj h7

/-! ============================================================================
   §4. 振幅单射 ⇒ 左可迁性（AxiomA + AxiomC + Finite C）
   ============================================================================

   核心思想：
     有限集合上，单射自映射是双射（Injective ↔ Surjective）。
     左乘映射 L_β 是单射（§3 已证），故是满射。
     满射意味着：对任意 γ，存在 α 使得 L_β(α) = γ。
     这正是左可迁性的定义。
   ============================================================================ -/

/-- **振幅单射 ⇒ 左可迁性**（W1 严格，有限性关键）。 -/
theorem amplitude_injective_implies_left_transitive
    [A : AxiomA M C] [Cx : AxiomC M C]
    [Finite C] [DecidableEq C]
    (h_inj : Function.Injective Cx.amplitude) :
    left_transitive (M := M) (C := C) := by
  intro γ β
  have h_inj' : Function.Injective (fun (α : C) => A.compose α β) :=
    amplitude_injective_implies_left_mul_injective (h_inj := h_inj) β
  have h_surj : Function.Surjective (fun (α : C) => A.compose α β) :=
    Finite.injective_iff_surjective.mp h_inj'
  rcases h_surj γ with ⟨α, hα⟩
  exact ⟨α, hα⟩

/-! ============================================================================
   §5. 两面性二分定理（综合结论）
   ============================================================================

   完整定理链：
     amplitude 单射
       ⇒ 左乘单射         (§3)
       ⇒ 左乘满射（有限性）
       ⇒ 左可迁性         (§4)
       ⇒ output 退化      (§2)

   因此在有限模型中，必有 output 退化 ∨ amplitude 非单射。
   这就是两面性二分：不存在两面平衡态。
   ============================================================================ -/

/-- **标准理论两面性二一定理**（W1 严格）。
    在满足 AxiomA + AxiomC 的有限模型中，
    以下两者必居其一：
      (a) output 是常函数（因果面退化）
      (b) amplitude 不是单射的（信息面退化）

    等价表述：不存在两面平衡态。 -/
theorem standard_theory_two_aspect_dichotomy
    [A : AxiomA M C] [Cx : AxiomC M C]
    [Finite C] [DecidableEq C] :
    (∀ (α β : C), A.output α = A.output β) ∨
    ¬ Function.Injective Cx.amplitude := by
  by_cases h_inj : Function.Injective Cx.amplitude
  · have h_left_trans : left_transitive (M := M) (C := C) :=
      amplitude_injective_implies_left_transitive h_inj
    have h_output_const : ∀ (α β : C), A.output α = A.output β :=
      output_degenerate_theorem h_left_trans
    left
    exact h_output_const
  · right
    exact h_inj

/-- **两面平衡态不可能性定理**（W1 严格，推论）。
    若 output 非平凡（∃ α β, output α ≠ output β），
    则 amplitude 不可能是单射的。 -/
theorem standard_theory_no_two_aspect_balance
    [A : AxiomA M C] [Cx : AxiomC M C]
    [Finite C] [DecidableEq C]
    (h_output_nontrivial : ∃ (α β : C), A.output α ≠ A.output β) :
    ¬ Function.Injective Cx.amplitude := by
  have h_dichotomy := standard_theory_two_aspect_dichotomy (M := M) (C := C)
  rcases h_dichotomy with (h_output_const | h_amp_not_inj)
  · rcases h_output_nontrivial with ⟨α, β, hne⟩
    have h_eq : A.output α = A.output β := h_output_const α β
    exact False.elim (hne h_eq)
  · exact h_amp_not_inj

/-! ============================================================================
   §6. 两面性定理的数学总结
   ============================================================================ -/

/-- **两面性定理综合**（W1 严格）。
    在 CSQIT 标准框架中：
      因果面非平凡 ⇒ 信息面退化
      信息面非平凡 ⇒ 因果面退化
      不存在两面平衡态。 -/
theorem two_aspect_summary
    [A : AxiomA M C] [Cx : AxiomC M C]
    [Finite C] [DecidableEq C] :
    ((∃ α β : C, A.output α ≠ A.output β) → ¬ Function.Injective Cx.amplitude) ∧
    ((Function.Injective Cx.amplitude) → (∀ α β : C, A.output α = A.output β)) := by
  constructor
  · intro hnontriv
    exact standard_theory_no_two_aspect_balance hnontriv
  · intro hinj
    have hlt := amplitude_injective_implies_left_transitive hinj
    exact output_degenerate_theorem hlt

end CSQIT_W1.TwoAspect
