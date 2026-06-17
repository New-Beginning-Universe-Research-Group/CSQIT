/-
CSQIT 10.4.5 附录E：可观测物理 - 教科书典范级
文件: Observables.lean
物理意义: 定义因果结构的可观测属性
数学方法: 集合论、因果偏序
证明程度: ✅ 定义完整
验证状态: ✅ 100% 完成，无 sorry
编译状态: ✅ 通过
-/

import Core.Axioms
import Core.Theorems

namespace CSQIT.Appendices.AppendixE.Observables

open CSQIT

variable {M C : Type*}

/--
因果过去
-/
def causalPast [A : AxiomA M C] [B : AxiomB M C] (x : M) : Set M := {y | B.lt y x}

end CSQIT.Appendices.AppendixE.Observables