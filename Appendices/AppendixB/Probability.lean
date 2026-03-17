/-
CSQIT 10.4.5 附录B：概率定义与因子化
文件: Probability.lean
内容: 概率定义、幺正性、概率因子化定理
版本: 10.4.5 (形式化验证完备版)
验证状态: ✅ 100% 完成，无 sorry
-/

import CSQIT.Appendices.AppendixB.TensorProduct

namespace CSQIT.Appendices.AppendixB

variable {A : AxiomA} {B : AxiomB A.M} {C : AxiomC A.C} {O : ColoredOperad A}

-- 概率定义（仅对闭合网络有意义）
def probability (φ : O.Operations [] []) : ℝ :=
  ‖amplitude_of_operation φ‖^2

-- 对闭合网络，概率必为1（由幺正性）
theorem prob_one_for_closed (φ : O.Operations [] []) :
    probability φ = 1 := by
  rw [probability, unitary_on_operad φ]
  norm_num

-- 概率因子化定理（对因果独立的闭合网络）
theorem probability_factorization
    (φ ψ : O.Operations [] [])
    (h_indep : causal_independent_ops φ ψ) :
    probability (tensor_product φ ψ h_indep) =
    probability φ * probability ψ := by
  rw [probability, probability, probability]
  rw [tensor_amplitude_rule φ ψ h_indep]
  rw [norm_mul, pow_two]
  ring

end CSQIT.Appendices.AppendixB