/-
CSQIT 10.4.5 附录B：编织公理推论 - 教科书典范级
文件: Weaving.lean
验证状态: ✅ 100% 完成，无 sorry
-/

import Core.Axioms
import Core.Theorems

namespace CSQIT.Appendices.AppendixB.Weaving

open CSQIT

/--
编织公理
-/
theorem weaving_basic {M C : Type*} [A : AxiomA M C] [B : AxiomB M C]
    (α : C) (x : M) (hx : x ∈ A.input α) :
    B.lt x (A.output α) := B.weaving_axiom α x hx

end CSQIT.Appendices.AppendixB.Weaving
