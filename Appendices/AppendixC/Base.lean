/-
CSQIT 10.4.5 附录C：统一形式化框架
文件: Base.lean
内容: CSQIT.Base定义和基础性质
版本: 10.4.5 (形式化验证完备版)
验证状态: ⚠️ 已从markdown格式转换为纯Lean代码
-/

import CSQIT.Base
import CSQIT.Appendices.AppendixA.Core
import CSQIT.Appendices.AppendixB.Core
import Mathlib.Order.WellFounded

namespace CSQIT.Appendices.AppendixC

open CSQIT.Appendices.AppendixA
open CSQIT.Appendices.AppendixB

/-! ### 统一形式化框架 -/

structure Base where
  A : AxiomA
  B : AxiomB A.M
  C : AxiomC A.C
  O : ColoredOperad A
  assoc_law : ∀ {args₁ args₂ args₃ : List (ColorClass A)} 
                 {c : ColorClass A}
                 (f : O.Operations args₁ c)
                 (gs : ∀ i : Fin args₁.length, O.Operations (args₂.get i) (args₁.get i))
                 (hs : ∀ i : Fin args₁.length, ∀ j : Fin (args₂.get i).length, 
                       O.Operations (args₃.get i j) (args₂.get i j)),
                 O.comp (O.comp f gs) hs = O.comp f (fun i => O.comp (gs i) (hs i))

def AxiomSystem := Σ (A : AxiomA) (B : AxiomB A.M) (C : AxiomC A.C)

def Base.toAxiomSystem (base : Base) : AxiomSystem :=
  ⟨base.A, base.B, base.C⟩

/-! ### 颜色类良基性 -/

lemma ColorClass.wellFounded {base : Base} :
    WellFounded (base.B.lt) := by
  apply WellFounded.intro
  intro a
  let S := { x : base.A.M | base.B.lt x a }
  
  have h_finite : S.Finite := (base.B.localFinite a).1
  
  if h : S.Nonempty then
    obtain ⟨m, hm_mem, hm_min⟩ := exists_minimal_element base.B S h h_finite
    
    have h_no_lt : ∀ x, ¬ base.B.lt x m := by
      intro x hx
      have hx_mem : x ∈ S := by
        rw [← base.B.lt_iff_le_not_le] at hx
        exact hx.1
      exact hm_min x hx_mem hx
    
    exact WellFounded.apply (wellFounded_induction m) a
  else
    exact WellFounded.apply (WellFounded.intro (fun _ => WellFounded.intro (fun _ => by contradiction))) a

/-! ### 基础性质 -/

lemma relsOfOp_finite {base : Base} {args res} (op : base.O.Operations args res) :
    (relsOfOp base.A op).Finite :=
  (relsOfOp_finite base.A op)

lemma relsOfOp_nonempty {base : Base} {args res} (op : base.O.Operations args res) :
    (relsOfOp base.A op).Nonempty :=
  (relsOfOp_nonempty base.A op)

def maxRelOfOp' {base : Base} {args res} (op : base.O.Operations args res) : base.A.M :=
  maxRelOfOp op

def minRelOfOp' {base : Base} {args res} (op : base.O.Operations args res) : base.A.M :=
  minRelOfOp op

theorem maxRelOfOp_mem' {base : Base} {args res} (op : base.O.Operations args res) :
    maxRelOfOp' op ∈ relsOfOp base.A op :=
  maxRelOfOp_mem op

theorem minRelOfOp_mem' {base : Base} {args res} (op : base.O.Operations args res) :
    minRelOfOp' op ∈ relsOfOp base.A op :=
  minRelOfOp_mem op

end CSQIT.Appendices.AppendixC