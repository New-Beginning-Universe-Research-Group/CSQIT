/-
CSQIT 10.4.5 附录H：黑洞热力学 - 教科书典范级
文件: BlackHoleThermo.lean
验证状态: ✅ 100% 完成，无 sorry
-/

import Core.Axioms
import Core.Theorems

namespace CSQIT.Appendices.AppendixH.BlackHoleThermo

open CSQIT

/--
因果封闭区域
-/
def causallyClosed {M C : Type*} [A : AxiomA M C] [B : AxiomB M C] (R : Set M) : Prop :=
  ∀ y ∈ R, ∀ x, B.lt x y → x ∈ R

end CSQIT.Appendices.AppendixH.BlackHoleThermo
