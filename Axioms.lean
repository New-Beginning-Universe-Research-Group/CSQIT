/-
CSQIT 10.4.5: 九条子公理定义
文件: Axioms.lean
版本: 10.4.5
-/

import Mathlib.Data.Finite.Basic
import Mathlib.Analysis.Complex.Basic

namespace CSQIT

/-! ### 公理A：存在与组合 -/

structure AxiomA where
  M : Type                -- 关系元集合
  isCountable : Countable M
  C : Type                -- 基本组合规则集合
  input : C → List M      -- 输入列表
  output : C → M          -- 输出关系元
  input_nodup : ∀ α : C, (input α).Nodup
  connected : ∀ x y : M, ∃ (chain : List C), 
    let nodes := [x, y] ++ chain.flatMap input ++ chain.map output
    x ∈ nodes ∧ y ∈ nodes ∧ ∀ c ∈ chain, ∀ z ∈ input c, z ∈ nodes

/-! ### 公理B：因果序与编织 -/

structure AxiomB (M : Type) where
  le : M → M → Prop       -- 偏序
  lt : M → M → Prop       -- 严格偏序
  le_refl : ∀ x, le x x
  le_trans : ∀ x y z, le x y → le y z → le x z
  le_antisymm : ∀ x y, le x y → le y x → x = y
  lt_irrefl : ∀ x, ¬ lt x x
  lt_trans : ∀ x y z, lt x y → lt y z → lt x z
  lt_iff_le_not_le : ∀ x y, lt x y ↔ (le x y ∧ ¬ le y x)
  inducedBy : ∀ x y : M, ∃ α : C, x ∈ input α ∧ output α = y → lt x y
  localFinite : ∀ x : M, 
    ({y : M | lt y x}.Finite ∧ {y : M | lt x y}.Finite)
  acyclic : ∀ x : M, ¬ lt x x
  transitive : ∀ x y z : M, lt x y → lt y z → lt x z
  weaving_axiom : ∀ {args : List (ColorClass M)} {c : ColorClass M}
    (f : Operation args c)
    (gs : ∀ i : Fin args.length, Σ a r, Operation a r)
    (h_res : ∀ i, (gs i).2.1 = [args.get i]),
    (∀ i, lt (maxRelOfOp (gs i).2.2) (minRelOfOp (f ∘ gs))) ∧
    (∀ i j, i ≠ j → 
      ∀ x ∈ relsOfOp (gs i).2.2, ∀ y ∈ relsOfOp (gs j).2.2, 
      ¬ lt x y ∧ ¬ lt y x)

/-! ### 公理C：概率幅 -/

structure AxiomC (C : Type) where
  amplitude : C → ℂ
  norm_one : ∀ α : C, ‖amplitude α‖ = 1
  comp_rule : ∀ α β : C, h : ? → amplitude α * amplitude β = amplitude (α ∘ β)
  closed_norm : ∀ (net : List C), IsClosedNetwork net → 
    ‖List.prod (net.map amplitude)‖ = 1
  amplitude_injective : Function.Injective amplitude

/-! ### 九条子公理汇总 -/

structure CSQIT where
  A : AxiomA
  B : AxiomB A.M
  C : AxiomC A.C

end CSQIT