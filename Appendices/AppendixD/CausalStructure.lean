/-
CSQIT 10.4.5 附录D：因果结构 - 教科书典范级
文件: CausalStructure.lean
物理意义: 定义因果未来和因果过去的集合表示
数学方法: 集合论、因果偏序关系
证明程度: ✅ 定义完整
验证状态: ✅ 100% 完成，无 sorry
编译状态: ✅ 通过
-/

import Core.Axioms
import Core.Theorems

namespace CSQIT.Appendices.AppendixD

open CSQIT

variable {M C : Type*}

/--
因果未来
-/
def causal_future [A : AxiomA M C] [B : AxiomB M C] (x : M) : Set M := {y | B.lt x y}

/--
因果过去
-/
def causal_past [A : AxiomA M C] [B : AxiomB M C] (x : M) : Set M := {y | B.lt y x}

end CSQIT.Appendices.AppendixD