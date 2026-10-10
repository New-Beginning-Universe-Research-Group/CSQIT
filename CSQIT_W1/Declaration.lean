/-
================================================================================
Declaration — CSQIT 的宣言与核心定理集中链
文件: CSQIT_W1/Declaration.lean
日期: 2026-10-10 (v4 — 可编译版本)
性质: 可编译文件。宣言 + 核心 theorem 链，来源标注。

编译前提: Foundation, MinimalCost, AttractorPrototype 的 olean 存在
         (本 session 已手动 build 这三个模块)

GenerationBridge 的编译错误是已有 bug，不在本 session scope 内修复。
================================================================================ -/

import CSQIT_W1.Foundation
import CSQIT_W1.MinimalCost
import CSQIT_W1.AttractorPrototype

namespace CSQIT_W1
open MinimalCost Foundation AttractorPrototype
open MinimalCost.WeavingBase

/-! ============================================================================
   宣言（短版）
   
   CSQIT = 4 个理论选择 + 一批 W1 严格推导
   
   理论选择：
     1. 三个群 A₄=12, A₅=60, PSL(2,7)=168
     2. α⁻¹ 公式形式 = p₁^p₄ + p₁^p₂ + 1 + p₂^p₁/(p₁·p₃^p₂)
     3. closure_N = lcm/2 中的 /2
     4. Ω 系列的公式结构
   
   诚实定位：
     既不是"从群论必然导出"（三个群和公式形式都是起点），
     也不是"数值巧合"（下游全部是严格 theorem）。
     它是从少数明确起点出发、下游严格自洽的数学结构。
   
   详情见 TheoryFoundations.lean。
   
   以下 theorem 全部带来源标注，均为 W1 严格。
   ============================================================================ -/

/-! ============================================================================
   A. closure 序列（Foundation, W1 严格）
   ============================================================================ -/

/-- **closure[0] = 8**（Foundation, W1 — 合取投影）。 -/
theorem declaration_closure0_eq_8 :
    closure_sequence_extended 0 = 8 := by
  exact closure_sequence_extended_values.1

/-- **closure[1] = 64**（Foundation, W1 — 合取投影）。 -/
theorem declaration_closure1_eq_64 :
    closure_sequence_extended 1 = 64 := by
  exact closure_sequence_extended_values.2.1

/-- **totalClosure = 420**（Foundation, W1）。 -/
theorem declaration_totalClosure_eq_420 :
    totalClosure = 420 := by
  exact totalClosure_eq_420

/-! ============================================================================
   B. MinimalCost 基底 mkBase（MinimalCost, W1 严格 — rfl）
   ============================================================================ -/

/-- **mkBase.p1 = 2**（MinimalCost, W1 — rfl）。 -/
theorem declaration_p1_eq_2 :
    mkBase.p1 = 2 := by rfl

/-- **mkBase.p2 = 3**（MinimalCost, W1 — rfl）。 -/
theorem declaration_p2_eq_3 :
    mkBase.p2 = 3 := by rfl

/-- **mkBase.p3 = 5**（MinimalCost, W1 — rfl）。 -/
theorem declaration_p3_eq_5 :
    mkBase.p3 = 5 := by rfl

/-- **mkBase.p4 = 7**（MinimalCost, W1 — rfl）。 -/
theorem declaration_p4_eq_7 :
    mkBase.p4 = 7 := by rfl

/-! ============================================================================
   C. α⁻¹ 公式与数值（W1 严格）
   
   来源: Foundation, MinimalCost, AttractorPrototype
   ============================================================================ -/

/-- **α⁻¹ = 137 + 9/250**（Foundation, W1）。 -/
theorem declaration_inverseAlpha_eq :
    inverseAlpha = 137 + 9 / 250 := by
  exact inverseAlpha_eq_137_036

/-- **MinimalCost.alpha_inv = 137 + 9/250**（MinimalCost, W1）。 -/
theorem declaration_alpha_inv_mkBase_eq :
    alpha_inv mkBase = 137 + 9 / 250 := by
  exact WeavingBase.alpha_inv_mkBase_eq_137p036

/-! ============================================================================
   D. attractor_unique（AttractorPrototype, W1 严格）
   
   给定公式形式 + 递增素数 → P 唯一锁定
   诚实边界：公式形式本身是理论选择，不是 CSQIT 推论
   ============================================================================ -/

/-- **attractor_unique**（AttractorPrototype, W1）。 -/
theorem declaration_attractor_unique :
    ∀ p₁ p₂ p₃ p₄ : ℕ,
    p₁ ≥ 2 → p₂ > p₁ → p₃ > p₂ → p₄ > p₃ →
    AttractorPrototype.alpha_integer_part p₁ p₂ p₄ = 137 →
    AttractorPrototype.alpha_fraction_eq p₁ p₂ p₃ →
    p₁ = 2 ∧ p₂ = 3 ∧ p₃ = 5 ∧ p₄ = 7 := by
  exact AttractorPrototype.attractor_unique

/-! ============================================================================
   E. 交叉验证：alpha_inv_mkBase_eq = inverseAlpha_eq（W1 严格）
   ============================================================================ -/

/-- **MinimalCost.alpha_inv mkBase = Foundation.inverseAlpha**（W1 严格恒等式）。 -/
theorem declaration_alpha_inv_consistency :
    alpha_inv mkBase = inverseAlpha := by
  rw [WeavingBase.alpha_inv_mkBase_eq_137p036, inverseAlpha_eq_137_036]

/-! ============================================================================
   F. closure_N = 2 × e₄ = 420（MinimalCost, W1 严格）
   ============================================================================ -/

/-- **e₄ = p₁·p₂·p₃·p₄ = 210**（MinimalCost, W1）。 -/
theorem declaration_e4_eq_210 :
    e4 mkBase = 210 := by
  exact WeavingBase.e4_mkBase_eq_210

/-- **closure_N = 2 × e₄**（MinimalCost, W1）。 -/
theorem declaration_closureN_eq_2e4 :
    closure_N mkBase = 2 * e4 mkBase := by
  exact WeavingBase.closure_N_is_2_times_e4

end CSQIT_W1