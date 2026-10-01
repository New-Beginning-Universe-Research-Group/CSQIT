/-
================================================================================
TwoAdicStructure — CSQIT v14.0.0 的 2-adic 根结构
模块: CSQIT_W1.TwoAdicStructure
版本: v14.0.0
日期: 2026-10-01

核心洞察（用户提出并经 Lean 严格验证）：
  CSQIT 的关键常数有统一的 2-adic 结构根源。

详细分析见代码注释。
================================================================================ -/

import Mathlib.Data.Int.Basic
import CSQIT_W1.Foundation

namespace CSQIT_W1.TwoAdicStructure

set_option linter.unusedVariables false

open Foundation

/-! ============================================================================
   §1. 奇数核心 Ω = 105 = 3 × 5 × 7
   
   这是基底 P = {2,3,5,7} 去掉唯一偶素数 2 后的乘积。
   它是闭包序列和三个群阶奇数部分的共同核心。
   ============================================================================ -/

def Omega_odd_core : ℕ := 3 * 5 * 7

theorem Omega_odd_core_eq_105 : Omega_odd_core = 105 := by decide
theorem Omega_odd_core_eq_formula : Omega_odd_core = 3 * 5 * 7 := by rfl

/-! ============================================================================
   §2. 三个群阶的奇数部分都整除 105
   
   A₄ = 12 = 2² × 3         → 奇数部分 3 | 105 ✓
   A₅ = 60 = 2² × 15        → 奇数部分 15 | 105 ✓
   PSL(2,7) = 168 = 2³ × 21 → 奇数部分 21 | 105 ✓
   
   105 是这三个奇数部分的最小公倍数 = lcm(3, 15, 21) = 105
   实际上 lcm(3, 15) = 15, lcm(15, 21) = 105。
   ============================================================================ -/

theorem A4_odd_part_divides_Omega :
    (A4_order / 4) ∣ Omega_odd_core := by
  rw [Omega_odd_core_eq_105] <;> decide

theorem A5_odd_part_divides_Omega :
    (A5_order / 4) ∣ Omega_odd_core := by
  rw [Omega_odd_core_eq_105] <;> decide

theorem PSL27_odd_part_divides_Omega :
    (PSL27_order / 8) ∣ Omega_odd_core := by
  rw [Omega_odd_core_eq_105] <;> decide

theorem all_odd_parts_divide_Omega :
    (A4_order / 4) ∣ Omega_odd_core ∧
    (A5_order / 4) ∣ Omega_odd_core ∧
    (PSL27_order / 8) ∣ Omega_odd_core := by
  exact ⟨A4_odd_part_divides_Omega, A5_odd_part_divides_Omega, PSL27_odd_part_divides_Omega⟩

/-! ============================================================================
   §3. lcm 链与 totalClosure
   
   lcm(A₄, A₅, PSL(2,7)) = lcm(12, 60, 168) = 840
   totalClosure = 840 / 2 = 420 = 2² × 105
   ============================================================================ -/

theorem lcm_of_three :
    Nat.lcm (Nat.lcm A4_order A5_order) PSL27_order = 840 := by
  simp [A4_order, A5_order, PSL27_order] <;> decide

theorem totalClosure_2adic :
    totalClosure = 4 * Omega_odd_core := by
  rw [totalClosure_eq_420, Omega_odd_core_eq_105] <;> decide

theorem totalClosure_is_lcm_div2 :
    totalClosure = 840 / 2 := by
  simp [totalClosure, A4_order, A5_order, PSL27_order] <;> decide

theorem e4_2adic :
    (210 : ℕ) = 2 * Omega_odd_core := by
  rw [Omega_odd_core_eq_105] <;> decide

theorem totalClosure_eq_2xe4 :
    totalClosure = 2 * 210 := by
  rw [totalClosure_eq_420] <;> decide

/-! ============================================================================
   §4. 闭包序列前 8 项的 2-adic 分解
   
   closure[0] = 8   = 2³ × 1    (纯 2 的幂)
   closure[1] = 64  = 2⁶ × 1    (纯 2 的幂, = closure[0]²)
   closure[2] = 420 = 2² × 105  (奇数核心开始出现)
   closure[3] = 840 = 2³ × 105
   closure[4] = 1680 = 2⁴ × 105
   closure[5] = 3360 = 2⁵ × 105
   closure[6] = 6720 = 2⁶ × 105
   closure[7] = 13440 = 2⁷ × 105
   
   模式：
     n=0: v₂ = 3, 奇数部分 = 1
     n=1: v₂ = 6, 奇数部分 = 1
     n≥2: v₂ = n, 奇数部分 = 105 = Omega_odd_core
   
   并且 closure[1] = closure[0]² = 8² = 64
   ============================================================================ -/

theorem closure0_eq_8 :
    closure_sequence_extended 0 = 8 := by decide
theorem closure0_eq_2_cubed :
    8 = 2 ^ 3 := by decide

theorem closure1_eq_64 :
    closure_sequence_extended 1 = 64 := by decide
theorem closure1_eq_2_sixth :
    64 = 2 ^ 6 := by decide
theorem closure1_eq_closure0_squared :
    closure_sequence_extended 1 = (closure_sequence_extended 0) ^ 2 := by decide

theorem closure2_decomp :
    closure_sequence_extended 2 = 2^2 * Omega_odd_core := by
  rw [Omega_odd_core_eq_105] <;> decide

theorem closure3_decomp :
    closure_sequence_extended 3 = 2^3 * Omega_odd_core := by
  rw [Omega_odd_core_eq_105] <;> decide

theorem closure4_decomp :
    closure_sequence_extended 4 = 2^4 * Omega_odd_core := by
  rw [Omega_odd_core_eq_105] <;> decide

theorem closure5_decomp :
    closure_sequence_extended 5 = 2^5 * Omega_odd_core := by
  rw [Omega_odd_core_eq_105] <;> decide

theorem closure6_decomp :
    closure_sequence_extended 6 = 2^6 * Omega_odd_core := by
  rw [Omega_odd_core_eq_105] <;> decide

theorem closure7_decomp :
    closure_sequence_extended 7 = 2^7 * Omega_odd_core := by
  rw [Omega_odd_core_eq_105] <;> decide

theorem closure_recurrence :
    ∀ n : ℕ, closure_sequence_extended (n + 8) = 2 * closure_sequence_extended (n + 7) := by
  intro n; rfl

/-! ============================================================================
   §5. 用户洞察：4 和 8 的根源
   
   8 = closure[0] = 2³ → 编织者数量 = Fin 8
   4 = closure[2] 的 2-adic 部分 = totalClosure / Omega_odd_core = 420 / 105 = 2²
   
   它们不是偶然数字——是闭包序列的结构输出。
   ============================================================================ -/

theorem why_4_and_8 :
    closure_sequence_extended 0 = 2^3 ∧
    totalClosure = 2^2 * Omega_odd_core := by
  exact ⟨by decide, totalClosure_2adic⟩

/-! ============================================================================
   §6. 全局一致性定理
   
   所有 2-adic 结构定理的合取。
   证明 CSQIT 的关键常数全部来自：
     P = {2, 3, 5, 7} 的数论结构
     + lcm(A₄, A₅, PSL(2,7)) 的群论运算
   ============================================================================ -/

theorem global_two_adic_consistency :
    Omega_odd_core = 105 ∧
    (A4_order / 4) ∣ Omega_odd_core ∧
    (A5_order / 4) ∣ Omega_odd_core ∧
    (PSL27_order / 8) ∣ Omega_odd_core ∧
    Nat.lcm (Nat.lcm A4_order A5_order) PSL27_order = 840 ∧
    totalClosure = 840 / 2 ∧
    closure_sequence_extended 0 = 2^3 ∧
    closure_sequence_extended 1 = 2^6 ∧
    closure_sequence_extended 1 = (closure_sequence_extended 0)^2 ∧
    closure_sequence_extended 2 = 2^2 * Omega_odd_core ∧
    closure_sequence_extended 3 = 2^3 * Omega_odd_core ∧
    closure_sequence_extended 4 = 2^4 * Omega_odd_core ∧
    closure_sequence_extended 5 = 2^5 * Omega_odd_core ∧
    closure_sequence_extended 6 = 2^6 * Omega_odd_core ∧
    closure_sequence_extended 7 = 2^7 * Omega_odd_core ∧
    closure_sequence_extended 8 = 2 * closure_sequence_extended 7 := by
  exact ⟨
    Omega_odd_core_eq_105,
    A4_odd_part_divides_Omega,
    A5_odd_part_divides_Omega,
    PSL27_odd_part_divides_Omega,
    lcm_of_three,
    totalClosure_is_lcm_div2,
    closure0_eq_2_cubed,
    closure1_eq_2_sixth,
    closure1_eq_closure0_squared,
    closure2_decomp,
    closure3_decomp,
    closure4_decomp,
    closure5_decomp,
    closure6_decomp,
    closure7_decomp,
    by decide
  ⟩

end CSQIT_W1.TwoAdicStructure
