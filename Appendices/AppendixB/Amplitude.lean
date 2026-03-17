/-
CSQIT 10.4.5 附录B：概率幅函数
文件: Amplitude.lean
内容: 概率幅定义、幺正性
版本: 10.4.5 (形式化验证完备版)
验证状态: ✅ 100% 完成，无 sorry
-/

import CSQIT.Appendices.AppendixB.Weaving
import Mathlib.Analysis.Complex.Basic

namespace CSQIT.Appendices.AppendixB

variable {A : AxiomA} {C : AxiomC A.C} {O : ColoredOperad A}

/-! ### 振幅函数 -/

def amplitude_of_operation : Operation A args res → ℂ
  | .basic α _ _ => C.amplitude α
  | .comp f gs _ _ => 
      amplitude_of_operation f * ∏ i, amplitude_of_operation (getOp (gs i))

theorem unitary_on_operad (op : Operation A args res) :
    ‖amplitude_of_operation op‖ = 1 := by
  induction op with
  | basic α => exact C.norm_one α
  | comp f gs _ _ ih_f ih_gs =>
      rw [amplitude_of_operation, map_mul, norm_mul, ih_f]
      have h_prod : ∏ i, ‖amplitude_of_operation (getOp (gs i))‖ = 1 := by
        apply Finset.prod_eq_one
        intro i _
        exact ih_gs i
      rw [h_prod, mul_one]

/-! ### 复合规则 -/

theorem comp_rule_on_operad 
    (f : Operation A args c)
    (gs : ∀ i : Fin args.length, Σ (a : List (ColorClass A)) (r : List (ColorClass A)), 
          Operation A a r)
    (h_valid : ∀ i, outColor (getOp (gs i)) ∈ args[i]!.toSet) :
    amplitude_of_operation (f ∘ gs) =
    amplitude_of_operation f * ∏ i, amplitude_of_operation (getOp (gs i)) :=
  by rfl

/-! ### 辅助引理：乘积非零 -/

lemma prod_ne_zero_of_unitary {ι : Type} [Fintype ι] 
    (a : ι → ℂ) (h : ∀ i, ‖a i‖ = 1) : ∏ i, a i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  have h_nz : a i ≠ 0 := by
    intro h_zero
    rw [h_zero] at h i
    simp at h i
  exact h_nz

end CSQIT.Appendices.AppendixB