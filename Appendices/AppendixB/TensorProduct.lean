/-
CSQIT 10.4.5 附录B：张量积接口
文件: TensorProduct.lean
内容: 张量积定义（为附录C预留接口）
版本: 10.4.5 (形式化验证完备版)
验证状态: ✅ 100% 完成（接口定义）
-/

import CSQIT.Appendices.AppendixB.Amplitude
import CSQIT.Appendices.AppendixC.TensorProduct

namespace CSQIT.Appendices.AppendixB

variable {A : AxiomA} {B : AxiomB A.M} {C : AxiomC A.C} {O : ColoredOperad A}

def tensor_product
    {args₁ res₁ args₂ res₂ : List (ColorClass A)}
    (f : O.Operations args₁ res₁)
    (g : O.Operations args₂ res₂)
    (h_indep : causal_independent_ops f g) :
    O.Operations (args₁ ++ args₂) (res₁ ++ res₂) :=
  CSQIT.Appendices.AppendixC.tensor_product_impl_detailed f g h_indep

theorem tensor_amplitude_rule
    {args₁ res₁ args₂ res₂ : List (ColorClass A)}
    (f : O.Operations args₁ res₁)
    (g : O.Operations args₂ res₂)
    (h_indep : causal_independent_ops f g) :
    amplitude_of_operation (tensor_product f g h_indep) =
    amplitude_of_operation f * amplitude_of_operation g :=
  CSQIT.Appendices.AppendixC.tensor_amplitude_rule_proven f g h_indep

end CSQIT.Appendices.AppendixB