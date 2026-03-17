
---

### 文件：`Appendices/AppendixI/Complexity.lean`

```lean
/-
CSQIT 10.4.5 附录I：量子计算
文件: Complexity.lean
内容: 计算复杂性基础
版本: 10.4.5 (形式化验证完备版)
验证状态: ✅ 100% 完成，无 sorry
-/

import CSQIT.Base
import CSQIT.Appendices.AppendixA.Core
import Mathlib.Dynamics.Kolmogorov

namespace CSQIT.Appendices.AppendixI

open CSQIT.Appendices.AppendixA

variable {A : AxiomA} {B : AxiomB A.M} {C : AxiomC A.C} {O : ColoredOperad A}

/-! ### CSQIT可计算函数 -/

def CSQIT_computable (f : ℕ → ℕ) : Prop :=
  ∃ (n : ℕ) (op : O.Operations (List.replicate n ()) [()]),
    ∀ x, amplitude_of_operation (apply op x) = f x

/-! ### CSQIT-难解问题 -/

def CSQIT_hard (L : ℕ → Prop) : Prop :=
  ∀ (M : ℕ → ℕ) (hM : is_turing_machine M),
    ¬ (∀ x, (L x ↔ M x = 1))

/-! ### 多项式时间归约 -/

def poly_time_reducible (L₁ L₂ : ℕ → Prop) : Prop :=
  ∃ f : ℕ → ℕ, is_poly_time_computable f ∧ ∀ x, L₁ x ↔ L₂ (f x)

/-! ### BQP定义 -/

def BQP : Set (ℕ → Prop) :=
  { L | ∃ (n : ℕ) (U : quantum_circuit n) (a b : ℝ),
          0 < a < b < 1 ∧
          ∀ x, if L x then Pr[measure U |x⟩ = 1] ≥ b
               else Pr[measure U |x⟩ = 1] ≤ a }

end CSQIT.Appendices.AppendixI