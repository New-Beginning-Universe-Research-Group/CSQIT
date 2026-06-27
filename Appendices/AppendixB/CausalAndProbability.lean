/-
CSQIT 10.5 附录B：因果序、概率与基础定义
文件: Appendices/AppendixB/CausalAndProbability.lean
版本: 10.5 (数学根本优化版)
日期: 2026-06-28
================================================================================
因果序的基本性质、概率定义以及其他基础定义。
================================================================================
-/

import Core.Axioms
import Core.Theorems
import Core.Models.FinModels
import Mathlib.Data.Complex.Basic

namespace CSQIT.Appendices.AppendixB

open CSQIT

/-! ============================================================================
   1. 因果序的基本性质
   ============================================================================ -/

/--
定理 B.1: 输入关系元因果先于输出关系元（编织公理）
**证明程度**: ✅ 完整证明
-/
theorem input_lt_output {M C : Type*} [A : AxiomA M C] [B : AxiomB M C]
    (α : C) (x : M) (hx : x ∈ A.input α) :
    B.lt x (A.output α) := B.weaving_axiom α x hx

/--
定理 B.2: 因果序不自反
**证明程度**: ✅ 完整证明
-/
theorem lt_irrefl {M C : Type*} [A : AxiomA M C] [B : AxiomB M C]
    (x : M) : ¬ B.lt x x := by
  intro h
  have h1 : B.le x x ∧ ¬ B.le x x := (B.lt_iff_le_not_le x x).mp h
  exact h1.2 h1.1

/--
定理 B.3: 因果序传递
**证明程度**: ✅ 完整证明
-/
theorem lt_trans {M C : Type*} [A : AxiomA M C] [B : AxiomB M C]
    (x y z : M) (hxy : B.lt x y) (hyz : B.lt y z) :
    B.lt x z := by
  have h1 : B.le x y ∧ ¬ B.le y x := (B.lt_iff_le_not_le x y).mp hxy
  have h2 : B.le y z ∧ ¬ B.le z y := (B.lt_iff_le_not_le y z).mp hyz
  have h_le_xz : B.le x z := B.le_trans x y z h1.1 h2.1
  have h_nle_zx : ¬ B.le z x := by
    intro h_zx
    have h_zy : B.le y x := B.le_trans y z x h2.1 h_zx
    exact h1.2 h_zy
  exact (B.lt_iff_le_not_le x z).mpr ⟨h_le_xz, h_nle_zx⟩

/-! ============================================================================
   2. 概率定义
   ============================================================================ -/

section Probability

variable (M C : Type) [A : AxiomA M C] [Cx : AxiomC M C]

/--
定义 B.1: 概率 = 振幅的模平方
**物理意义**: 从量子振幅定义概率
-/
def probability (α : C) : ℝ := Complex.normSq (Cx.amplitude α)

/--
定理 B.4: 每个规则的概率恒为1
**证明程度**: ✅ 完整证明
**注**: 这反映了振幅的幺正性，即每个规则本身是"归一化"的。
        概率的非平凡性需要在测量或系综层面体现。
-/
theorem probability_eq_one (α : C) : probability M C α = 1 := by
  simp [probability]
  <;> exact Cx.norm_one α

end Probability

/-! ============================================================================
   3. 量子接口定理
   ============================================================================ -/

/--
定理 B.5: 振幅幺正性
物理意义: CSQIT 振幅对应量子力学中的归一化量子态
数学陈述: |amplitude(α)|² = 1（幺正条件）
**证明程度**: ✅ 完整证明
-/
theorem amplitude_is_unit {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α : C) : Complex.normSq (Cx.amplitude α) = 1 :=
  Cx.norm_one α

/--
定理 B.6: 振幅组合律
物理意义: CSQIT 规则组合对应量子态的张量积
数学陈述: amplitude(α∘β) = amplitude(α) · amplitude(β)
**证明程度**: ✅ 完整证明
-/
theorem amplitude_composition {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α β : C) : Cx.amplitude (A.compose α β) = Cx.amplitude α * Cx.amplitude β :=
  Cx.comp_rule α β

/--
定理 B.7: 振幅非零性
物理意义: 量子态永远非零（物理意义明确）
数学陈述: amplitude(α) ≠ 0
**证明程度**: ✅ 完整证明
-/
theorem quantum_state_nonzero {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α : C) : Cx.amplitude α ≠ 0 := by
  intro h
  have h₁ : Complex.normSq (Cx.amplitude α) = 1 := Cx.norm_one α
  rw [h] at h₁
  simp [Complex.normSq] at h₁

/--
定理 B.8: 信息编码唯一性
物理意义: 不同量子态编码不同信息
数学陈述: amplitude 是单射函数
**证明程度**: ✅ 完整证明
-/
theorem information_encoding_unique {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C] :
    Function.Injective Cx.amplitude :=
  Cx.amplitude_injective

/--
定理 B.9: 信息守恒定理
物理意义: 组合操作保持信息量（乘法性）
数学陈述: 信息量(α∘β) = 信息量(α) · 信息量(β)
**证明程度**: ✅ 完整证明
-/
theorem information_conservation {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α β : C) :
    Complex.normSq (Cx.amplitude (A.compose α β)) =
    Complex.normSq (Cx.amplitude α) * Complex.normSq (Cx.amplitude β) := by
  simp only [Cx.norm_one (A.compose α β), Cx.norm_one α, Cx.norm_one β, one_mul]

/-! ============================================================================
   4. 基础定义
   ============================================================================ -/

/--
定义 B.2: 规则的关系元集合
输入关系元 ∪ {输出关系元}
-/
def relsOfRule {M C : Type*} [A : AxiomA M C] (α : C) : Set M :=
  {x | x ∈ A.input α} ∪ {A.output α}

end CSQIT.Appendices.AppendixB
