/-
CSQIT 10.5 附录D：因果结构
文件: Appendices/AppendixD/CausalStructure.lean
版本: 10.5 (数学根本优化版)
日期: 2026-06-28
================================================================================
因果未来、因果过去的定义及基本性质。
================================================================================
-/

import Core.Axioms
import Core.Theorems

namespace CSQIT.Appendices.AppendixD

open CSQIT

variable {M C : Type*}

/-! ============================================================================
   1. 因果未来与因果过去
   ============================================================================ -/

/--
定义 D.1: 因果未来
所有严格因果后于 x 的关系元集合
-/
def causal_future [A : AxiomA M C] [B : AxiomB M C] (x : M) : Set M := {y | B.lt x y}

/--
定义 D.2: 因果过去
所有严格因果先于 x 的关系元集合
-/
def causal_past [A : AxiomA M C] [B : AxiomB M C] (x : M) : Set M := {y | B.lt y x}

/-! ============================================================================
   2. 基本性质
   ============================================================================ -/

/--
定理 D.1: 因果未来的单调性
若 x ≤ y，则 future(y) ⊆ future(x)
**证明程度**: ✅ 完整证明
-/
theorem causal_future_mono [A : AxiomA M C] [B : AxiomB M C]
    {x y : M} (hxy : B.le x y) :
    (causal_future (M := M) (C := C) y) ⊆ (causal_future (M := M) (C := C) x) := by
  intro z hz
  have h1 : B.lt y z := hz
  have h2 : B.lt x z := by
    have h3 : B.le x y := hxy
    have h4 : B.le y z := (B.lt_iff_le_not_le y z).mp h1 |>.1
    have h5 : B.le x z := B.le_trans x y z h3 h4
    have h6 : ¬ B.le z x := by
      intro h7
      have h8 : B.le z y := B.le_trans z x y h7 h3
      exact (B.lt_iff_le_not_le y z).mp h1 |>.2 h8
    exact (B.lt_iff_le_not_le x z).mpr ⟨h5, h6⟩
  exact h2

/--
定理 D.2: 因果过去的单调性
若 x ≤ y，则 past(x) ⊆ past(y)
**证明程度**: ✅ 完整证明
-/
theorem causal_past_mono [A : AxiomA M C] [B : AxiomB M C]
    {x y : M} (hxy : B.le x y) :
    (causal_past (M := M) (C := C) x) ⊆ (causal_past (M := M) (C := C) y) := by
  intro z hz
  have h1 : B.lt z x := hz
  have h2 : B.lt z y := by
    have h3 : B.le z x := (B.lt_iff_le_not_le z x).mp h1 |>.1
    have h4 : B.le x y := hxy
    have h5 : B.le z y := B.le_trans z x y h3 h4
    have h6 : ¬ B.le y z := by
      intro h7
      have h8 : B.le x z := B.le_trans x y z h4 h7
      exact (B.lt_iff_le_not_le z x).mp h1 |>.2 h8
    exact (B.lt_iff_le_not_le z y).mpr ⟨h5, h6⟩
  exact h2

end CSQIT.Appendices.AppendixD
