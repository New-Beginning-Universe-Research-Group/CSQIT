/-
CSQIT 10.4.5: 基础定义
文件: Base.lean
版本: 10.4.5
-/

import CSQIT.Axioms

namespace CSQIT

/-! ### 颜色类定义 -/

def colorEquiv {A : AxiomA} (x y : A.M) : Prop :=
  ∃ (chain : List A.C), 
    let nodes := [x, y] ++ chain.flatMap A.input ++ chain.map A.output
    x ∈ nodes ∧ y ∈ nodes ∧
    ∀ c ∈ chain, ∀ z ∈ A.input c, z ∈ nodes

theorem colorEquiv_is_equivalence {A : AxiomA} : 
    Equivalence (@colorEquiv A) :=
  ⟨fun x => ⟨[], by simp⟩,
   fun h => ⟨h.choose, h.choose_spec.2.1, h.choose_spec.1, h.choose_spec.2.2⟩,
   fun hxy hyz => ⟨hxy.choose ++ hyz.choose, by simp⟩⟩

def ColorClass (A : AxiomA) : Type :=
  Quotient (colorEquiv_is_equivalence (A:=A))

/-! ### 操作定义 -/

inductive Operation (A : AxiomA) : 
    List (ColorClass A) → List (ColorClass A) → Type where
  | basic (α : A.C) : 
      Operation A (A.input α |>.map (·.toColorClass)) [A.output α |>.toColorClass]
  | comp {args₁ res₁ : List (ColorClass A)} {args₂ : List (List (ColorClass A))}
      (f : Operation A args₁ res₁)
      (gs : ∀ i : Fin args₁.length, 
            Σ (a : List (ColorClass A)) (r : List (ColorClass A)), 
            Operation A a r)
      (h_args : ∀ i, (gs i).1 = args₂.get i)
      (h_res : ∀ i, (gs i).2.1 = [args₁.get i]) :
      Operation A (args₂.join) res₁

def getOp {a r} (p : Σ (args : List (ColorClass A)) (res : List (ColorClass A)), 
    Operation A args res) : Operation A p.1 p.2.1 := p.2.2

def M.toColorClass {A : AxiomA} (x : A.M) : ColorClass A := Quotient.mk'' x

end CSQIT