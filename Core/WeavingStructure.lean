/-
================================================================================
CSQIT 10.4.5 核心模块 - 编织结构 (Weaving Structure)
文件: Core/WeavingStructure.lean

本模块将编织统一为 WeavingStructure 类。
================================================================================
-/

import Core.Axioms

namespace CSQIT

-- ============================================================================
-- 编织结构的抽象定义
-- ============================================================================

/-- **编织结构 (Weaving Structure)**:

编织是 CSQIT 中从三个基本结构中涌现的复合性质：
- 因果序 (AxiomB)
- 代数复合 (AxiomA)
- 量子振幅 (AxiomC)
-/

class WeavingStructure (M C : Type*) [A : AxiomA M C] [B : AxiomB M C] [Cx : AxiomC M C] where
  /-- Hom α β 表示从 α 到 β 的编织路径 -/
  Hom : C → C → Type*

  /-- 恒等编织路径 -/
  id : ∀ (α : C), Hom α α

  /-- 编织路径的复合 -/
  comp : ∀ (α β γ : C), Hom α β → Hom β γ → Hom α γ

  /-- 振幅在编织复合下可乘 -/
  amplitude_comp : ∀ {α β γ : C} (f : Hom α β) (g : Hom β γ),
    Cx.amplitude γ = Cx.amplitude α * Cx.amplitude β

-- ============================================================================
-- 范畴论编织 (OperadicWeaving)
-- ============================================================================

/-- **OperadicWeaving**: 范畴论版本的编织结构（强化版）

使用 AxiomA'（非平凡 output）实现非空洞实例化
-/

structure OperadicWeaving (M C : Type*) [A : AxiomA M C] [B : AxiomB M C] [Cx : AxiomC M C] where
  Hom : C → C → Type*
  id : ∀ (α : C), Hom α α
  comp : ∀ (α β γ : C), Hom α β → Hom β γ → Hom α γ
  amplitude_comp : ∀ {α β γ : C} (f : Hom α β) (g : Hom β γ),
    Cx.amplitude γ = Cx.amplitude α * Cx.amplitude β
  complete_from_causal : ∀ (α β : C),
    B.lt (A.output α) (A.output β) → Nonempty (Hom α β)

-- ============================================================================
-- OperadicWeaving 使用 AxiomA'
-- ============================================================================

/-- **OperadicWeaving'**: 使用 AxiomA'（独立公理，包含完整 input/output/compose/combine）
    实现非空洞实例化。关键区别：output 非退化，complete_from_causal 有真实前提。 -/

structure OperadicWeaving' (M C : Type*) [A' : AxiomA' M C] [B : AxiomB M C] [Cx' : AxiomC' M C] where
  Hom : C → C → Type*
  id : ∀ (α : C), Hom α α
  comp : ∀ (α β γ : C), Hom α β → Hom β γ → Hom α γ
  amplitude : C → ℂ
  comp_functorial : ∀ {α β γ : C} (f : Hom α β) (g : Hom β γ),
    amplitude γ = amplitude α * amplitude β
  faithful : ∀ {α β : C} (f g : Hom α β), f = g
  complete_from_causal : ∀ (α β : C),
    B.lt (A'.output α) (A'.output β) → Nonempty (Hom α β)

end CSQIT
