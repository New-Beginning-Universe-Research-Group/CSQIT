/-
CSQIT 10.5 附录J：数学基础与代数结构
文件: Appendices/AppendixJ/Mathematics.lean
版本: 10.5 (数学根本优化版)
日期: 2026-06-28
================================================================================
CSQIT 公理体系的数学结构性质：
- 规则组合构成半群
- 振幅映射是半群同态
- 振幅的单位圆群性质
- 因果序的偏序性质
================================================================================
-/

import Core.Axioms
import Core.Theorems
import Core.WeavingStructure
import Mathlib.Data.Complex.Basic

namespace CSQIT.Appendices.AppendixJ.Mathematics

open CSQIT

/-! ============================================================================
   1. 规则组合的半群结构
   ============================================================================ -/

/--
定理 J.1: 组合结合律
规则组合构成半群
**证明程度**: ✅ 完整证明
-/
theorem compose_assoc {M C : Type*} [A : AxiomA M C]
    (α β γ : C) : A.compose (A.compose α β) γ = A.compose α (A.compose β γ) :=
  A.compose_assoc α β γ

/--
定理 J.2: 振幅结合律的保持
振幅在组合下保持结合律
**证明程度**: ✅ 完整证明
-/
theorem amplitude_assoc_preserved {M C : Type*}
    [A : AxiomA M C] [Cx : AxiomC M C] (α β γ : C) :
    Cx.amplitude (A.compose (A.compose α β) γ) =
    Cx.amplitude (A.compose α (A.compose β γ)) := by
  rw [Cx.comp_rule (A.compose α β) γ, Cx.comp_rule α (A.compose β γ),
      Cx.comp_rule α β, Cx.comp_rule β γ]
  ring

/-! ============================================================================
   2. 振幅的群性质（单位圆 U(1)）
   ============================================================================ -/

/--
定理 J.3: 振幅模方恒为1
振幅构成单位圆群 U(1)
**证明程度**: ✅ 完整证明
-/
theorem amplitude_unit_circle {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α : C) : Complex.normSq (Cx.amplitude α) = 1 :=
  Cx.norm_one α

/--
定理 J.4: 振幅乘法的封闭性
单位复数在乘法下封闭
**证明程度**: ✅ 完整证明
-/
theorem amplitude_mul_closed (z₁ z₂ : ℂ)
    (h₁ : Complex.normSq z₁ = 1) (h₂ : Complex.normSq z₂ = 1) :
    Complex.normSq (z₁ * z₂) = 1 := by
  simp only [Complex.normSq, Complex.mul_re, Complex.mul_im]
  have hr₁ : z₁.re * z₁.re + z₁.im * z₁.im = 1 := by
    have := h₁
    simp only [Complex.normSq] at this
    exact this
  have hr₂ : z₂.re * z₂.re + z₂.im * z₂.im = 1 := by
    have := h₂
    simp only [Complex.normSq] at this
    exact this
  calc (z₁.re * z₂.re - z₁.im * z₂.im) * (z₁.re * z₂.re - z₁.im * z₂.im) +
        (z₁.re * z₂.im + z₁.im * z₂.re) * (z₁.re * z₂.im + z₁.im * z₂.re)
      = (z₁.re * z₁.re + z₁.im * z₁.im) * (z₂.re * z₂.re + z₂.im * z₂.im) := by ring
      _ = 1 * 1 := by rw [hr₁, hr₂]
      _ = 1 := by ring

/--
定理 J.5: 振幅映射是半群同态
amplitude : (C, compose) → (ℂ, *) 是半群同态
**证明程度**: ✅ 完整证明
-/
theorem amplitude_is_semigroup_hom {M C : Type*}
    [A : AxiomA M C] [Cx : AxiomC M C] (α β : C) :
    Cx.amplitude (A.compose α β) = Cx.amplitude α * Cx.amplitude β :=
  Cx.comp_rule α β

/-! ============================================================================
   3. 存在论基础
   ============================================================================ -/

/--
定理 J.8: 关系元非空
关系元集合非空，存在论基础
**证明程度**: ✅ 完整证明
-/
theorem rels_nonempty {M C : Type*} [A : AxiomA M C] (α : C) : Nonempty M := ⟨A.output α⟩

/-! ============================================================================
   4. 因果序的偏序性质
   ============================================================================ -/

/--
定理 J.6: 因果序的传递性
因果关系形成严格的因果链
**证明程度**: ✅ 完整证明
-/
theorem causal_order_transitive {M C : Type*} [A : AxiomA M C] [B : AxiomB M C]
    (x y z : M) (hxy : B.lt x y) (hyz : B.lt y z) : B.lt x z := by
  have h1 : B.le x y ∧ ¬ B.le y x := (B.lt_iff_le_not_le x y).mp hxy
  have h2 : B.le y z ∧ ¬ B.le z y := (B.lt_iff_le_not_le y z).mp hyz
  have h3 : B.le x z := B.le_trans x y z h1.1 h2.1
  have h4 : ¬ B.le z x := by
    intro h
    have h5 : B.le z y := B.le_trans z x y h h1.1
    exact h2.2 h5
  exact (B.lt_iff_le_not_le x z).mpr ⟨h3, h4⟩

/--
定理 J.7: 因果序的严格性（反自反）
没有任何事件因果先于自己
**证明程度**: ✅ 完整证明
-/
theorem causal_order_irreflexive {M C : Type*} [A : AxiomA M C] [B : AxiomB M C]
    (x : M) : ¬ B.lt x x := by
  intro h
  have h1 : B.le x x ∧ ¬ B.le x x := (B.lt_iff_le_not_le x x).mp h
  exact h1.2 h1.1

end CSQIT.Appendices.AppendixJ.Mathematics
