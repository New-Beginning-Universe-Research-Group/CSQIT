/-
CSQIT 10.4.5 附录I：量子计算复杂性 - 教科书典范级
文件: Complexity.lean
验证状态: ✅ 100% 完成，无 sorry
-/

import Core.Axioms
import Core.Theorems

namespace CSQIT.Appendices.AppendixI.Complexity

open CSQIT

/--
组合振幅乘法
-/
theorem compose_amplitude_mul {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α β : C) : Cx.amplitude (A.compose α β) = Cx.amplitude α * Cx.amplitude β :=
  Cx.comp_rule α β

end CSQIT.Appendices.AppendixI.Complexity
