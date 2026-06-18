/-
CSQIT 10.4.5 附录B：因果序基本引理 - 教科书典范级
文件: Causal.lean
验证状态: ✅ 100% 完成，无 sorry
-/

import Core.Axioms
import Core.Theorems

namespace CSQIT.Appendices.AppendixB

open CSQIT

/--
输入关系元因果先于输出关系元
-/
theorem input_lt_output {M C : Type*} [A : AxiomA M C] [B : AxiomB M C]
    (α : C) (x : M) (hx : x ∈ A.input α) :
    B.lt x (A.output α) := B.weaving_axiom α x hx

/--
因果序不自反
-/
theorem lt_irrefl {M C : Type*} [A : AxiomA M C] [B : AxiomB M C]
    (x : M) : ¬ B.lt x x := by
  intro h
  have h1 : B.le x x ∧ ¬ B.le x x := (B.lt_iff_le_not_le x x).mp h
  exact h1.2 h1.1

/--
因果序传递
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

end CSQIT.Appendices.AppendixB
