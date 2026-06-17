/-
CSQIT 10.4.5 附录B：核心定义 - 教科书典范级
文件: BasicDefinitions.lean
验证状态: ✅ 100% 完成，无 sorry
-/

import Core.Axioms
import Core.Theorems

namespace CSQIT.Appendices.AppendixB.BasicDefinitions

open CSQIT

/--
规则的关系元集合
-/
def relsOfRule {M C : Type*} [A : AxiomA M C] (α : C) : Set M :=
  {x | x ∈ A.input α} ∪ {A.output α}

end CSQIT.Appendices.AppendixB.BasicDefinitions
