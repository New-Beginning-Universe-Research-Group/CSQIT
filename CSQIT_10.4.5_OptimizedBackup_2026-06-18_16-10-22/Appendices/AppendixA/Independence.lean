/-
📝 附录A：公理体系的基本推论
文件: Appendices/AppendixA/Independence.lean
================================================================================
本文件包含 Core.Axioms 中公理的直接重述推论。
关于"公理独立性"的严格证明需要构造反例模型，这超出了本文件范围。
================================================================================
-/

import Core.Axioms
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic

namespace CSQIT.Appendices.AppendixA.Independence

open CSQIT

/-! ============================================================================
   1. AxiomA 的直接推论（字段重述）
   ============================================================================ -/

/--
推论 A.11: compose 的结合律（AxiomA.compose_assoc 的直接重述）
-/
theorem compose_assoc_from_axiom {M C : Type*} [A : AxiomA M C] (α β γ : C) :
    A.compose (A.compose α β) γ = A.compose α (A.compose β γ) :=
  A.compose_assoc α β γ

/--
推论 A.12: compose_input 的一致性（AxiomA.compose_input 的直接重述）
-/
theorem compose_input_consistency {M C : Type*} [A : AxiomA M C] (α β : C) :
    A.input (A.compose α β) = A.input α ++ A.input β :=
  A.compose_input α β

/--
推论 A.13: compose_output 的一致性（AxiomA.compose_output 的直接重述）
-/
theorem compose_output_consistency {M C : Type*} [A : AxiomA M C] (α β : C) :
    A.output (A.compose α β) = A.output β :=
  A.compose_output α β

/-! ============================================================================
   2. AxiomB 的直接推论（字段重述）
   ============================================================================ -/

/--
推论 A.14: 因果偏序的自反性（AxiomB.le_refl 的直接重述）
-/
theorem causal_le_refl {M C : Type*} [A : AxiomA M C] [B : AxiomB M C] (x : M) :
    B.le x x := B.le_refl x

/--
推论 A.15: 因果偏序的传递性（AxiomB.le_trans 的直接重述）
-/
theorem causal_le_trans {M C : Type*} [A : AxiomA M C] [B : AxiomB M C]
    (x y z : M) (hxy : B.le x y) (hyz : B.le y z) : B.le x z :=
  B.le_trans x y z hxy hyz

/--
推论 A.16: 因果偏序的反对称性（AxiomB.le_antisymm 的直接重述）
-/
theorem causal_le_antisymm {M C : Type*} [A : AxiomA M C] [B : AxiomB M C]
    (x y : M) (hxy : B.le x y) (hyx : B.le y x) : x = y :=
  B.le_antisymm x y hxy hyx

/-! ============================================================================
   3. 备注
   ============================================================================ -/

/-
说明:
  关于公理独立性（即某个公理不能从其他公理推出）的严格证明
  需要构造反例模型，这涉及 typeclass 实例推断的复杂交互。
  本文件不包含此类证明。
-/

end CSQIT.Appendices.AppendixA.Independence
