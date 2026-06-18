/-
================================================================================
CSQIT 10.4.5 - AxiomD 独立性证明
文件: Core/AxiomD_Independence.lean
版本: 10.4.5 (Canonical Textbook Edition)
日期: 2026-06-18

================================================================================
核心理论成果
================================================================================

本文件证明 AxiomD（操作编织的局部一致性）独立于 AxiomA + AxiomB。

**核心洞察**：
通过构造一个反模型，我们展示存在满足 AxiomA + AxiomB 但不满足 AxiomD 的数学结构。
这意味着 AxiomD 不能从 AxiomA 和 AxiomB 推导出来——它引入了真正的新约束。

**反模型设计思想**：
我们故意让 compose 函数的像是（image）小于规则空间 C，
从而制造一个"因果裂缝"：虽然 output α < output β（因果序成立），
但不存在任何 γ 使得 compose α γ = β（编织路径不存在）。

================================================================================
-/

import Core.Axioms
import Core.Theorems
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic

namespace CSQIT.AxiomD_Independence

open CSQIT

/-
================================================================================
反模型构造
================================================================================

**关系元空间 M = {m0, m1}**
- 提供非平凡的因果偏序：m0 < m1
- 这是最简单的非平凡偏序结构

**规则空间 C = {a, b, c}**
- a, b, c 是三种不同的操作规则
- 我们故意设计使得 c 无法被"生成"
- compose 函数的像是 {a, b}，不包含 c
- 这制造了关键的"因果裂缝"

**output 函数设计**：
- output(a) = m0
- output(b) = m1
- output(c) = m1
- 因此 lt(output a)(output c) = lt(m0)(m1) = True（因果序成立）

**compose 函数设计**：
- compose(_, a) = a
- compose(_, b) = b
- compose(_, c) = b（关键：对任何 α，compose α c 都返回 b）
- 因此 compose(a, c) = b ≠ c，c 永远无法被生成

**结果**：
- 前提成立：lt(output a)(output c) = True
- 但不存在 γ 使得 compose(a, γ) = c
- AxiomD 被违反：AxiomD 要求若 output α < output β，则存在 γ 使得 compose α γ = β
- 然而 AxiomA 和 AxiomB 的其他约束都被满足

这正是我们要找的"因果裂缝"——满足 A+B 但不满足 D。
================================================================================
-/

inductive TestC | a | b | c

instance : DecidableEq TestC :=
  fun x y =>
    match x, y with
    | TestC.a, TestC.a => isTrue rfl
    | TestC.b, TestC.b => isTrue rfl
    | TestC.c, TestC.c => isTrue rfl
    | TestC.a, TestC.b => isFalse (fun h => by cases h)
    | TestC.a, TestC.c => isFalse (fun h => by cases h)
    | TestC.b, TestC.a => isFalse (fun h => by cases h)
    | TestC.b, TestC.c => isFalse (fun h => by cases h)
    | TestC.c, TestC.a => isFalse (fun h => by cases h)
    | TestC.c, TestC.b => isFalse (fun h => by cases h)

inductive TestM | m0 | m1

instance : DecidableEq TestM :=
  fun x y =>
    match x, y with
    | TestM.m0, TestM.m0 => isTrue rfl
    | TestM.m1, TestM.m1 => isTrue rfl
    | TestM.m0, TestM.m1 => isFalse (fun h => by cases h)
    | TestM.m1, TestM.m0 => isFalse (fun h => by cases h)

/- **因果偏序关系**：
   - m0 ≤ m0, m0 ≤ m1, m1 ≤ m1 成立
   - m1 ≤ m0 不成立（因为 m1 > m0）
   - 这是严格偏序：自反、传递、反对称
-/
def testM_le (x y : TestM) : Prop :=
  match x, y with
  | TestM.m0, TestM.m0 => True
  | TestM.m0, TestM.m1 => True
  | TestM.m1, TestM.m0 => False
  | TestM.m1, TestM.m1 => True

/-
**严格因果序**：
- lt(m0)(m0) = False（不严格早于自己）
- lt(m0)(m1) = True（m0 严格早于 m1）
- lt(m1)(m0) = False（m1 不早于 m0）
- lt(m1)(m1) = False（不严格早于自己）
-/
def testM_lt (x y : TestM) : Prop :=
  match x, y with
  | TestM.m0, TestM.m0 => False
  | TestM.m0, TestM.m1 => True
  | TestM.m1, TestM.m0 => False
  | TestM.m1, TestM.m1 => False

/-
================================================================================
定理: axiomD_independent_of_AB
================================================================================

**目标**: 证明存在模型满足 AxiomA + AxiomB 但不满足 AxiomD。

**证明策略**:
1. 构造反模型 (M=TestM, C=TestC)
2. 定义满足 AxiomA 的所有字段
3. 定义满足 AxiomB 的所有字段
4. 证明关键引理:
   - h_lt: lt(output a)(output c) = lt(m0)(m1) = True
   - h_not_exists: 不存在 γ 使得 compose(a, γ) = c
5. 构造存在性声明

**形式化**:
axiomD_independent_of_AB : ∃ (M C : Type) (instA : AxiomA M C) (instB : AxiomB M C),
  ∃ (α β : C),
    (instB.lt (instA.output α) (instA.output β)) ∧
    (¬ ∃ (γ : C), instA.compose α γ = β)
================================================================================
-/
theorem axiomD_independent_of_AB :
  ∃ (M C : Type) (instA : AxiomA M C) (instB : AxiomB M C),
    ∃ (α β : C),
      (instB.lt (instA.output α) (instA.output β)) ∧
      (¬ ∃ (γ : C), instA.compose α γ = β) := by
  let M := TestM
  let C := TestC
  
  /- **input 函数**: 所有规则的输入都为空列表
     这与 input_must_be_empty 定理一致 -/
  let input : C → List M := fun _ => []
  
  /- **output 函数**: 关键设计
     - a → m0
     - b → m1
     - c → m1
     这创建了因果序：m0 < m1 -/
  let output : C → M := fun
    | TestC.a => TestM.m0
    | TestC.b => TestM.m1
    | TestC.c => TestM.m1
  
  /- **compose 函数**: 核心设计
     通过让 compose(_, c) = b，我们确保 c 永远无法被"生成"
     compose 的像是 {a, b}，不包含 c
     这制造了因果裂缝 -/
  let compose : C → C → C := fun α β =>
    match β with
    | TestC.a => TestC.a
    | TestC.b => TestC.b
    | TestC.c => TestC.b
  
  have input_nodup : ∀ α : C, (input α).Nodup := by
    intro α
    exact List.nodup_nil
  
  have compose_input : ∀ α β : C, input (compose α β) = input α ++ input β := by
    intro α β
    rfl
  
  have compose_output : ∀ α β : C, output (compose α β) = output β := by
    intro α β
    cases β
    rfl
    rfl
    rfl
  
  have compose_assoc : ∀ α β γ : C, compose (compose α β) γ = compose α (compose β γ) := by
    intro α β γ
    cases β <;> cases γ <;> rfl
  
  let instA : AxiomA M C := {
    input := input,
    output := output,
    input_nodup := input_nodup,
    compose := compose,
    compose_input := compose_input,
    compose_output := compose_output,
    compose_assoc := compose_assoc
  }
  
  let le := testM_le
  let lt := testM_lt
  
  have le_refl : ∀ x : M, le x x := by
    intro x; cases x <;> trivial
  
  have le_trans : ∀ x y z : M, le x y → le y z → le x z := by
    intro x y z hxy hyz
    cases x <;> cases y <;> cases z <;> trivial
  
  have le_antisymm : ∀ x y : M, le x y → le y x → x = y := by
    intro x y hxy hyx
    cases x <;> cases y <;> trivial
  
  have le_m0_m0 : le TestM.m0 TestM.m0 := trivial
  have le_m1_m1 : le TestM.m1 TestM.m1 := trivial
  
  have lt_iff_le_not_le : ∀ x y : M, lt x y ↔ (le x y ∧ ¬ le y x) := by
    intro x y
    cases x
    case m0 =>
      cases y
      case m0 =>
        exact Iff.intro (fun h => False.elim h) (fun h => absurd le_m0_m0 h.2)
      case m1 =>
        exact Iff.intro (fun _ => ⟨trivial, fun h => h⟩) (fun _ => trivial)
    case m1 =>
      cases y
      case m0 =>
        exact Iff.intro (fun h => False.elim h) (fun h => False.elim h.1)
      case m1 =>
        exact Iff.intro (fun h => False.elim h) (fun h => absurd le_m1_m1 h.2)
  
  have localFinite_past : ∀ x : M, Set.Finite {y : M | lt y x} := by
    intro x
    cases x
    case m0 =>
      have : {y : M | lt y TestM.m0} = ∅ := by
        ext y
        cases y
        case m0 => exact Iff.intro (fun h => False.elim h) (fun h => False.elim h)
        case m1 => exact Iff.intro (fun h => False.elim h) (fun h => False.elim h)
      rw [this]
      exact Set.finite_empty
    case m1 =>
      have : {y : M | lt y TestM.m1} = {TestM.m0} := by
        ext y
        cases y
        case m0 => exact Iff.intro (fun _ => Set.mem_singleton TestM.m0) (fun h => by trivial)
        case m1 => exact Iff.intro (fun h => False.elim h) (fun h => False.elim (by rw [Set.mem_singleton_iff] at h; cases h))
      rw [this]
      exact Set.finite_singleton TestM.m0

  have localFinite_future : ∀ x : M, Set.Finite {y : M | lt x y} := by
    intro x
    cases x
    case m0 =>
      have : {y : M | lt TestM.m0 y} = {TestM.m1} := by
        ext y
        cases y
        case m0 => exact Iff.intro (fun h => False.elim h) (fun h => False.elim (by rw [Set.mem_singleton_iff] at h; cases h))
        case m1 => exact Iff.intro (fun _ => Set.mem_singleton TestM.m1) (fun h => by trivial)
      rw [this]
      exact Set.finite_singleton TestM.m1
    case m1 =>
      have : {y : M | lt TestM.m1 y} = ∅ := by
        ext y
        cases y
        case m0 => exact Iff.intro (fun h => False.elim h) (fun h => False.elim h)
        case m1 => exact Iff.intro (fun h => False.elim h) (fun h => False.elim h)
      rw [this]
      exact Set.finite_empty
  
  have weaving_axiom : ∀ (α : C) (x : M), x ∈ instA.input α → lt x (instA.output α) := by
    intro α x hx
    cases α <;> cases x <;> cases hx
  
  let instB : AxiomB M C := {
    le := le,
    lt := lt,
    le_refl := le_refl,
    le_trans := le_trans,
    le_antisymm := le_antisymm,
    lt_iff_le_not_le := lt_iff_le_not_le,
    localFinite_past := localFinite_past,
    localFinite_future := localFinite_future,
    weaving_axiom := weaving_axiom
  }
  
  /- **关键引理 1**: 前提成立
     lt(output a)(output c) = lt(m0)(m1) = True -/
  have h_lt : instB.lt (instA.output TestC.a) (instA.output TestC.c) := by
    have oa : instA.output TestC.a = TestM.m0 := rfl
    have oc : instA.output TestC.c = TestM.m1 := rfl
    rw [oa, oc]
    exact trivial
  
  /- **关键引理 2**: 不存在 γ 使得 compose(a, γ) = c
     分情况讨论：
     - compose(a, a) = a ≠ c
     - compose(a, b) = b ≠ c
     - compose(a, c) = b ≠ c -/
  have h_not_exists : ¬ ∃ (γ : C), instA.compose TestC.a γ = TestC.c := by
    intro h
    cases h with
    | intro γ hγ =>
      cases γ
      have : instA.compose TestC.a TestC.a = TestC.a := rfl
      rw [this] at hγ
      exact absurd hγ (by decide : TestC.a ≠ TestC.c)
      have : instA.compose TestC.a TestC.b = TestC.b := rfl
      rw [this] at hγ
      exact absurd hγ (by decide : TestC.b ≠ TestC.c)
      have : instA.compose TestC.a TestC.c = TestC.b := rfl
      rw [this] at hγ
      exact absurd hγ (by decide : TestC.b ≠ TestC.c)
  
  exact ⟨M, C, instA, instB, TestC.a, TestC.c, h_lt, h_not_exists⟩

/-
================================================================================
开放问题: axiomD_independent_of_ABC
================================================================================

要证明 AxiomD 独立于 AxiomA + AxiomB + AxiomC，需要构造一个同时满足 A+B+C
但仍不满足 D 的模型。这需要：

1. 为上述反模型添加 AxiomC 实例（例如 amplitude ≡ 1）
2. 证明 amplitude 满足 norm_one, comp_rule, amplitude_injective
3. 验证 AxiomD 仍然被违反

这是一个重要的后续工作，将关闭核心理论中的最后一个逻辑缺口。
================================================================================
-/
def axiomD_independent_of_ABC : Prop :=
  ∃ (M C : Type) (instA : AxiomA M C) (instB : AxiomB M C) (_ : AxiomC M C),
    ∃ (α β : C),
      (instB.lt (instA.output α) (instA.output β)) ∧
      (¬ ∃ (γ : C), instA.compose α γ = β)

end CSQIT.AxiomD_Independence
