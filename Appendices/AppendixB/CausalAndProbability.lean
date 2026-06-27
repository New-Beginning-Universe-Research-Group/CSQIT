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
   3. 基础定义
   ============================================================================ -/

/--
定义 B.2: 规则的关系元集合
输入关系元 ∪ {输出关系元}
-/
def relsOfRule {M C : Type*} [A : AxiomA M C] (α : C) : Set M :=
  {x | x ∈ A.input α} ∪ {A.output α}

end CSQIT.Appendices.AppendixB
