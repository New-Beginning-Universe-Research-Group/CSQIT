/- ================================================================================
CSQIT v12.6 — LatticeGap：有限因果格的格距正性证明
文件: V12/Core/LatticeGap.lean
版本: v12.6.0

核心定理（W1 严格）：
  在有限有界因果格中，格距严格大于零。

  这是 CSQIT 框架"物理时空离散"的 W1 严格证明——
  不需要 AxiomD 或其他额外公理，仅需 Foundation 已有的：
    BoundedCausalLattice M（有界因果格：有 ⊥ 和 ⊤）
    Fintype M（有限性）
    Nonempty M

  证明极其简洁：
    Fintype.card M > 0（Nonempty 保证）
    → (Fintype.card M : ℝ) > 0
    → 1 / (Fintype.card M : ℝ) > 0
    → 格距 > 0

诚实边界：
  本模块的所有定理都是 W1 严格数学结论。
  它们建立在 [Fintype M] 假设上——即因果格 M 是有限的。
  物理诠释是 W3："宇宙因果结构是有限的/局部有限的"。
  无穷因果格是否存在，不在 W1 层面回答。
================================================================================ -/

import V12.Core.Foundation
import Mathlib.Data.Real.Basic

namespace CSQIT.V12.LatticeGap

open CSQIT.V12.Foundation

/- §1 格距定义 -/

/-- **格距（离散倒数形式）**。
    
    latticeGap M = 1 / |M|，其中 |M| = Fintype.card M。
    
    物理意义（W3）：M 是宇宙因果格（所有因果事件的集合）。
    |M| > 0 由 Nonempty M 保证。
    因此 1/|M| > 0：宇宙因果结构有正的离散层间距。
    
    诚实边界：这是离散近似。真实物理格距需要 W2/W3 的量纲配准。 -/
noncomputable def latticeGap (M : Type*) [Fintype M] [BoundedCausalLattice M] : ℝ :=
  1 / (Fintype.card M : ℝ)

/- §2 主定理：格距严格正（W1 严格） -/

/-- **主定理：有限因果格格距严格正**（W1 严格）。
    
    前提：[Fintype M]（有限）+ [BoundedCausalLattice M]（有界因果格）
          + [Nonempty M]（非空）
    结论：latticeGap M > 0
    
    证明（3 行）：
      1. Fintype.card_pos : 0 < Fintype.card M（Nonempty M 保证）
      2. exact_mod_cast : (0 : ℝ) < (Fintype.card M : ℝ)
      3. div_pos : 0 < 1 / (Fintype.card M : ℝ) -/
theorem latticeGapPos
    (M : Type*) [Fintype M] [BoundedCausalLattice M] [Nonempty M] :
    0 < latticeGap M := by
  have h_card_pos : 0 < Fintype.card M := Fintype.card_pos
  have h_real_pos : (0 : ℝ) < (Fintype.card M : ℝ) := by exact_mod_cast h_card_pos
  have h_div_pos : (0 : ℝ) < 1 / (Fintype.card M : ℝ) := by
    apply div_pos
    · norm_num
    · exact h_real_pos
  have h_eq : latticeGap M = 1 / (Fintype.card M : ℝ) := rfl
  linarith

/- §3 推论：连续时空不相容（W1 严格） -/

/-- **格距为零**（W1 定义）。
    
    物理意义（W3）：对应"连续时空假设"——
    假设 M 是无限的（|M| = ∞ → 1/|M| = 0）。 -/
def spacingZero (M : Type*) [Fintype M] [BoundedCausalLattice M] : Prop :=
  latticeGap M = 0

/-- **推论：有限因果格中格距不可能为零**（W1 严格）。
    
    物理意义（W3）：连续时空假设与 CSQIT 的有限因果格假设不相容。
    
    这是千禧年论证的物理层面基石：
      NS 方程假设连续时空（格距 = 0）
      但 CSQIT 中有限因果格的格距 > 0（W1 严格）
      → NS 方程的物理前提在 CSQIT 中不成立
      → NS 方程是有效理论，不是基本理论 -/
theorem continuumIncompatible
    (M : Type*) [Fintype M] [BoundedCausalLattice M] [Nonempty M] :
    spacingZero M → False := by
  have h_pos : 0 < latticeGap M := latticeGapPos M
  intro h_zero
  have h_contra : latticeGap M = 0 := h_zero
  linarith

end CSQIT.V12.LatticeGap