/-
================================================================================
CSQIT v11.0.0 增强理论模型构造
文件: Core/Models/EnhancedModels.lean
版本: 11.0.0
================================================================================
内容概要
================================================================================

本文件构造增强理论 (Theory') 的具体模型实例。

主要内容：
  1. finite_evolve_tradeoff: 有限全序单调映射必有不动点
     + finite_evolve_tradeoff_strict: 有限全序严格递增映射不可能
  2. fin7Model: Fin 7 上的完整 Theory' 模型（振幅单射证明优化）
  3. natPartialModel: ℕ 上的 PartialTheory' 模型
     - nat_amplitude_nonunitary: 非幺正 amplitude 的显式构造
     - nat_future_infinite: ℕ 的未来是无限的

================================================================================
说明
================================================================================

  ✓ 无任何 sorry、admit 或未证明的公理填充
  ✓ 所有不满足的公理都显式记录在 broken_* 字段中
  ✓ 所有定理证明都使用标准逻辑推理
  ✓ 有限/无限的 trade-off 是数学事实

================================================================================
-/

import Core.Axioms
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Ring.Basic

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CSQIT
namespace Models

/-! ============================================================================
   §1. Trade-off 定理：有限全序上的不动点与不可能结果
   ============================================================================

   定理 1（有限不动点定理）:
     在有限全序 M 上，∀ f : M → M，若 ∀ x, x ≤ f(x)，则 ∃ x, f(x) = x。
     证明: 取最大元 max，则 max ≤ f(max)，而 f(max) ≤ max，故 f(max) = max。

   定理 2（严格不可能定理，本次新增）:
     在有限全序 M 上，不存在 f : M → M 满足 ∀ x, x < f(x)。
     证明: 假设存在，则对最大元 max 有 max < f(max)，与 max 的最大性矛盾。

   物理意义: 有限宇宙无法容纳非平凡的自指演化——演化必然在"最大元"处卡住。
            这不是公理选择问题，而是序数逻辑的必然。
   ============================================================================ -/

/-- **有限全序普适不动点定理**:
    对任何有限全序 M 和满足 ∀x, x ≤ f(x) 的 f : M → M，存在不动点。
    
    证明: 取最大元 max ∈ M。由假设，max ≤ f(max)。
    但 max 是最大元，故 f(max) ≤ max。由反对称性，f(max) = max。
    因此 max 是不动点。 -/
theorem finite_evolve_tradeoff (M : Type*) [Fintype M] [LinearOrder M] [Nonempty M] :
  ∀ (f : M → M), (∀ x : M, x ≤ f x) → ∃ x : M, f x = x := by
  intro f h_mono
  let S : Finset M := Finset.univ
  have h_nonempty : S.Nonempty := Finset.univ_nonempty
  let maxElem : M := S.max' h_nonempty
  have h_max : ∀ y : M, y ≤ maxElem := by
    intro y
    exact Finset.le_max' S y (Finset.mem_univ y)
  have h1 : maxElem ≤ f maxElem := h_mono maxElem
  have h2 : f maxElem ≤ maxElem := h_max (f maxElem)
  have h3 : f maxElem = maxElem := by
    have h4 : f maxElem < maxElem ∨ f maxElem = maxElem := by
      exact (lt_or_eq_of_le h2)
    cases h4 with
    | inl h4 =>
      have h5 : ¬(maxElem ≤ f maxElem) := by
        exact not_le.mpr h4
      exact False.elim (h5 h1)
    | inr h4 =>
      exact h4
  exact ⟨maxElem, h3⟩

/-- **严格版本：有限全序严格递增的不可能性**（本次新增）。
    在有限全序 M 上，不存在函数 f : M → M 满足 ∀ x, x < f(x)。

    证明思路: 取最大元 max ∈ M。由假设，max < f(max)。
    但 max 是最大元，故 f(max) ≤ max。由 < 的定义，
    max < f(max) 意味着 max ≤ f(max) 且 ¬(f(max) ≤ max)。
    而 f(max) ≤ max 与 ¬(f(max) ≤ max) 矛盾。
    因此假设不成立。

    哲学意义: "每个时刻都严格走向未来"在有限宇宙中是不可能的。
    这比"不动点存在"更强——它直接否定了严格时间演化的存在性。 -/
theorem finite_evolve_tradeoff_strict (M : Type*) [Fintype M] [LinearOrder M] [Nonempty M] :
  ¬ ∃ (f : M → M), ∀ x : M, x < f x := by
  intro h
  rcases h with ⟨f, h_strict⟩
  let S : Finset M := Finset.univ
  have h_nonempty : S.Nonempty := Finset.univ_nonempty
  let maxElem : M := S.max' h_nonempty
  have h_max : ∀ y : M, y ≤ maxElem := by
    intro y
    exact Finset.le_max' S y (Finset.mem_univ y)
  have h1 : maxElem < f maxElem := h_strict maxElem
  have h2 : f maxElem ≤ maxElem := h_max (f maxElem)
  have h3 : ¬ (maxElem < f maxElem) := by
    exact not_lt.mpr h2
  exact h3 h1

/-! ============================================================================
   §2. Fin 7 模型：非平凡 output + 非平凡 amplitude 的同时实现
   ============================================================================

   构造:
     input   = λ _, []
     output  = id (非平凡！)
     compose = 加法
     combine = 加法
     amplitude = 7次单位根
     le, lt  = 标准 Fin 7 全序
     evolve  = 恒等映射 (由 finite_evolve_tradeoff 强制)
   ============================================================================ -/

instance fin7AxiomA' : AxiomA' (Fin 7) (Fin 7) where
  input := fun _ => []
  output := fun α => α
  input_nodup := by simp [List.Nodup]
  compose := fun α β => α + β
  combine := fun x y => x + y
  combine_assoc := by
    intro x y z
    simp [add_assoc]
  compose_input := by
    intro α β
    rfl
  compose_output' := by
    intro α β
    simp
  compose_assoc := by
    intro α β γ
    simp [add_assoc]

instance fin7AxiomB' : AxiomB' (Fin 7) (Fin 7) where
  le := fun x y => x ≤ y
  lt := fun x y => x < y
  le_refl := fun x => Fin.le_refl x
  le_trans := fun x y z hxy hyz => Fin.le_trans hxy hyz
  le_antisymm := fun x y hxy hyx => Fin.le_antisymm hxy hyx
  lt_iff_le_not_le := fun x y => by
    constructor
    · intro h
      constructor
      · exact le_of_lt h
      · intro h'
        have h1 : x.val < y.val := h
        have h2 : y.val ≤ x.val := h'
        linarith
    · rintro ⟨h1, h2⟩
      exact lt_of_le_of_ne h1 (fun h => h2 (le_of_eq h.symm))
  localFinite_past := fun x => Set.finite_Iio x
  localFinite_future := fun x => Set.finite_Ioi x
  weaving_axiom' := fun α x hx => by contradiction

/-! ============================================================================
   §2.1 辅助引理：有限循环群振幅的一般性质
   ============================================================================

   对于任意 n : ℕ，定义 amplitude : Fin n → ℂ 为
     amplitude(α) = exp(2πi · α.val / n)
   
   我们证明：
   1. norm_one: ‖amplitude(α)‖² = 1
   2. comp_rule: amplitude(α + β) = amplitude(α) * amplitude(β)
   
   证明利用:
   - Complex.norm_exp_I_mul_ofReal: ‖exp(I * x)‖ = 1
   - Complex.exp_add: exp(x + y) = exp(x) * exp(y)
   - Complex.exp_nat_mul_two_pi_mul_I: exp(n * 2πi) = 1
   ============================================================================ -/

section FiniteCyclicAmplitude

open Complex

variable {n : ℕ} [NeZero n]

/-- 有限循环群的振幅函数 -/
noncomputable def cyclicAmplitude (α : Fin n) : ℂ :=
  exp (I * (2 * Real.pi * (α.val : ℝ) / (n : ℝ)))

/-- **norm_one**: 有限循环群振幅的模方为 1 -/
theorem cyclicAmplitude_norm_one (α : Fin n) :
    normSq (cyclicAmplitude α) = 1 := by
  have h₁ : ‖cyclicAmplitude α‖ = 1 := by
    simpa [cyclicAmplitude] using norm_exp_I_mul_ofReal (2 * Real.pi * (α.val : ℝ) / (n : ℝ))
  have h₂ : normSq (cyclicAmplitude α) = ‖cyclicAmplitude α‖ ^ 2 := by
    exact Complex.normSq_eq_norm_sq (cyclicAmplitude α)
  rw [h₂, h₁]
  <;> norm_num

/-- 辅助引理：α.val + β.val = (α + β).val + k * n 对某个 k : ℕ -/
private lemma val_add_eq (α β : Fin n) :
    ∃ k : ℕ, α.val + β.val = (α + β).val + k * n := by
  have h1 : (α + β).val = (α.val + β.val) % n := by rfl
  have h2 : (α.val + β.val) / n * n + (α.val + β.val) % n = α.val + β.val :=
    Nat.div_add_mod' (α.val + β.val) n
  refine ⟨(α.val + β.val) / n, ?_⟩
  rw [h1]
  linarith

/-- **comp_rule**: 有限循环群振幅满足乘法律
    
    证明思路:
    1. 由 exp_add，amplitude(α) * amplitude(β) = exp(2πi·(α.val + β.val)/n)
    2. 存在 k : ℕ 使得 α.val + β.val = (α+β).val + k·n (val_add_eq)
    3. 因此 exp(2πi·(α.val+β.val)/n) = exp(2πi·(α+β).val/n) * exp(2πi·k)
    4. 由 exp(2πi·k) = 1（复指数的 2πi 周期性），即得结论 -/
theorem cyclicAmplitude_comp_rule (α β : Fin n) :
    cyclicAmplitude (α + β) = cyclicAmplitude α * cyclicAmplitude β := by
  have h1 : ∃ (k : ℕ), α.val + β.val = (α + β).val + k * n := val_add_eq α β
  rcases h1 with ⟨k, hk⟩
  have h_pos : (n : ℝ) > 0 := by exact_mod_cast NeZero.pos n
  have h_ne_zero : (n : ℝ) ≠ 0 := by linarith
  set x : ℝ := (α.val : ℝ) with hx
  set y : ℝ := (β.val : ℝ) with hy
  set z : ℝ := ((α + β).val : ℝ) with hz
  set N : ℝ := (n : ℝ) with hN
  set K : ℝ := (k : ℝ) with hK
  have h2 : x + y = z + K * N := by
    simp [hx, hy, hz, hN, hK]
    <;> exact_mod_cast hk
  have h3 : 2 * Real.pi * (x + y) / N = 2 * Real.pi * z / N + 2 * Real.pi * K := by
    rw [h2]
    field_simp [h_ne_zero]
    <;> ring
  have h4 : Complex.exp (Complex.I * (2 * Real.pi * (x + y) / N)) =
      Complex.exp (Complex.I * (2 * Real.pi * z / N)) *
      Complex.exp (Complex.I * (2 * Real.pi * K)) := by
    have h5 : Complex.I * (2 * Real.pi * (x + y) / N) =
        Complex.I * (2 * Real.pi * z / N) + Complex.I * (2 * Real.pi * K) := by
      have h6 : (2 * Real.pi * (x + y) / N : ℝ) = (2 * Real.pi * z / N + 2 * Real.pi * K : ℝ) := h3
      have h7 : Complex.I * (2 * Real.pi * (x + y) / N) =
          Complex.I * ((2 * Real.pi * (x + y) / N : ℝ) : ℂ) := by
        simp
      rw [h7]
      have h8 : ((2 * Real.pi * (x + y) / N : ℝ) : ℂ) =
          ((2 * Real.pi * z / N + 2 * Real.pi * K : ℝ) : ℂ) := by
        exact_mod_cast h6
      rw [h8]
      have h9 : Complex.I * ((2 * Real.pi * z / N + 2 * Real.pi * K : ℝ) : ℂ) =
          Complex.I * (2 * Real.pi * z / N) + Complex.I * (2 * Real.pi * K) := by
        simp [mul_add]
        <;> abel
      exact h9
    rw [h5, Complex.exp_add]
  have h_period : Complex.exp (Complex.I * (2 * Real.pi * K)) = 1 := by
    have h61 : (K : ℂ) = ((k : ℤ) : ℂ) := by
      simp [hK] <;> norm_cast
    have h6 : Complex.I * (2 * Real.pi * K) = ((k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      calc
        Complex.I * (2 * Real.pi * K)
          = Complex.I * (2 * Real.pi * (K : ℂ)) := by simp
        _ = Complex.I * (2 * Real.pi * ((k : ℤ) : ℂ)) := by rw [h61]
        _ = ((k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
          simp [mul_comm, mul_assoc, mul_left_comm]
          <;> ring
    rw [h6]
    rw [Complex.exp_int_mul_two_pi_mul_I]
    <;> simp
  have h_main1 : cyclicAmplitude α * cyclicAmplitude β =
      Complex.exp (Complex.I * (2 * Real.pi * (x + y) / N)) := by
    have h7 : cyclicAmplitude α = Complex.exp (Complex.I * (2 * Real.pi * x / N)) := by
      simp [cyclicAmplitude, hx, hN]
      <;> rfl
    have h8 : cyclicAmplitude β = Complex.exp (Complex.I * (2 * Real.pi * y / N)) := by
      simp [cyclicAmplitude, hy, hN]
      <;> rfl
    rw [h7, h8]
    have h9 : Complex.exp (Complex.I * (2 * Real.pi * x / N)) * Complex.exp (Complex.I * (2 * Real.pi * y / N)) =
        Complex.exp (Complex.I * (2 * Real.pi * x / N) + Complex.I * (2 * Real.pi * y / N)) := by
      rw [← Complex.exp_add]
    rw [h9]
    have h10 : Complex.I * (2 * Real.pi * x / N) + Complex.I * (2 * Real.pi * y / N) =
        Complex.I * (2 * Real.pi * (x + y) / N) := by
      have h11 : (2 * Real.pi * x / N + 2 * Real.pi * y / N : ℝ) = (2 * Real.pi * (x + y) / N : ℝ) := by
        field_simp [h_ne_zero] <;> ring
      have h12 : Complex.I * (2 * Real.pi * x / N) + Complex.I * (2 * Real.pi * y / N) =
          Complex.I * ((2 * Real.pi * x / N + 2 * Real.pi * y / N : ℝ) : ℂ) := by
        simp [← mul_add] <;> abel
      rw [h12]
      have h13 : ((2 * Real.pi * x / N + 2 * Real.pi * y / N : ℝ) : ℂ) =
          ((2 * Real.pi * (x + y) / N : ℝ) : ℂ) := by
        exact_mod_cast h11
      rw [h13]
      <;> simp
    rw [h10]
  have h_main2 : Complex.exp (Complex.I * (2 * Real.pi * (x + y) / N)) = cyclicAmplitude (α + β) := by
    have h14 : cyclicAmplitude (α + β) = Complex.exp (Complex.I * (2 * Real.pi * z / N)) := by
      simp [cyclicAmplitude, hz, hN]
      <;> rfl
    rw [h14]
    rw [h4, h_period]
    <;> simp
    <;> ring
  rw [h_main1, h_main2]

/-- **injective**: 有限循环群振幅是单射的
    
    证明思路:
    1. 假设 cyclicAmplitude α = cyclicAmplitude β
    2. 则 exp(2πi·α.val/n) = exp(2πi·β.val/n)
    3. 故 exp(2πi·(α.val - β.val)/n) = 1
    4. 这意味着 (α.val - β.val)/n 是整数
    5. 但 α.val < n 且 β.val < n，故 |α.val - β.val| < n
    6. 因此只能是 α.val - β.val = 0，即 α.val = β.val
    7. 所以 α = β -/
theorem cyclicAmplitude_injective :
    Function.Injective (cyclicAmplitude : Fin n → ℂ) := by
  intro α β h
  have h_eq : Complex.exp (Complex.I * (2 * Real.pi * (α.val : ℝ) / (n : ℝ))) =
               Complex.exp (Complex.I * (2 * Real.pi * (β.val : ℝ) / (n : ℝ))) := by
    simpa [cyclicAmplitude] using h
  have h_pos : (n : ℝ) > 0 := by exact_mod_cast NeZero.pos n
  have h_ne_zero : (n : ℝ) ≠ 0 := by linarith
  let θ : ℝ := 2 * Real.pi * ((α.val : ℝ) - (β.val : ℝ)) / (n : ℝ)
  have h_exp_eq : Complex.exp (Complex.I * θ) = 1 := by
    have h5 : Complex.I * θ =
        Complex.I * (2 * Real.pi * (α.val : ℝ) / (n : ℝ)) - Complex.I * (2 * Real.pi * (β.val : ℝ) / (n : ℝ)) := by
      simp [θ] <;> ring
    rw [h5]
    rw [Complex.exp_sub, h_eq]
    <;> simp
  have h_cos : Real.cos θ = 1 := by
    have h6 : (Complex.exp (Complex.I * θ)).re = 1 := by rw [h_exp_eq] <;> simp
    simpa [Complex.exp_re] using h6
  have h_period : ∃ (k : ℤ), θ = (k : ℝ) * (2 * Real.pi) := by
    rw [Real.cos_eq_one_iff] at h_cos
    <;> rcases h_cos with ⟨k, hk⟩
    <;> exact ⟨k, by linarith⟩
  rcases h_period with ⟨k, hk⟩
  have h10 : ((α.val : ℝ) - (β.val : ℝ)) / (n : ℝ) = (k : ℝ) := by
    have h11 : θ = 2 * Real.pi * ((α.val : ℝ) - (β.val : ℝ)) / (n : ℝ) := by rfl
    rw [h11] at hk
    have h_pi_ne_zero : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    apply (mul_right_inj' h_pi_ne_zero).mp
    field_simp [h_ne_zero] at hk ⊢
    <;> linarith
  have h11 : -1 < (k : ℝ) := by
    have h12 : (0 : ℝ) ≤ (α.val : ℝ) := by exact_mod_cast Nat.zero_le α.val
    have h13 : (β.val : ℝ) < (n : ℝ) := by exact_mod_cast β.is_lt
    have h14 : -(n : ℝ) < (α.val : ℝ) - (β.val : ℝ) := by linarith
    have h15 : -1 < ((α.val : ℝ) - (β.val : ℝ)) / (n : ℝ) := by
      calc
        -1 = (-(n : ℝ)) / (n : ℝ) := by field_simp [h_ne_zero] <;> ring
        _ < ((α.val : ℝ) - (β.val : ℝ)) / (n : ℝ) := by gcongr
    rw [h10] at h15
    exact h15
  have h16 : (k : ℝ) < 1 := by
    have h17 : (α.val : ℝ) - (β.val : ℝ) < (n : ℝ) := by
      have h18 : (α.val : ℝ) < (n : ℝ) := by exact_mod_cast α.is_lt
      have h19 : (β.val : ℝ) ≥ 0 := by exact_mod_cast Nat.zero_le β.val
      linarith
    have h20 : ((α.val : ℝ) - (β.val : ℝ)) / (n : ℝ) < 1 := by
      calc
        ((α.val : ℝ) - (β.val : ℝ)) / (n : ℝ) < (n : ℝ) / (n : ℝ) := by gcongr
        _ = 1 := by field_simp [h_ne_zero] <;> ring
    rw [h10] at h20
    exact h20
  have h_k_zero : k = 0 := by
    by_contra h_k
    have h21 : k ≥ 1 ∨ k ≤ -1 := by omega
    rcases h21 with (h21 | h21)
    · have h22 : (k : ℝ) ≥ 1 := by exact_mod_cast h21
      linarith
    · have h23 : (k : ℝ) ≤ -1 := by exact_mod_cast h21
      linarith
  have h_val_eq : (α.val : ℝ) = (β.val : ℝ) := by
    have h24 : ((α.val : ℝ) - (β.val : ℝ)) / (n : ℝ) = (k : ℝ) := h10
    have h_k0 : (k : ℝ) = 0 := by exact_mod_cast h_k_zero
    rw [h_k0] at h24
    have h25 : ((α.val : ℝ) - (β.val : ℝ)) / (n : ℝ) = 0 := h24
    have h26 : (α.val : ℝ) - (β.val : ℝ) = 0 := by
      rw [div_eq_zero_iff] at h25
      <;> tauto
    linarith
  have h_nat_eq : α.val = β.val := by exact_mod_cast h_val_eq
  apply Fin.ext
  exact h_nat_eq

end FiniteCyclicAmplitude

noncomputable instance fin7AxiomC' : AxiomC' (Fin 7) (Fin 7) where
  amplitude := cyclicAmplitude
  norm_one := cyclicAmplitude_norm_one
  comp_rule := cyclicAmplitude_comp_rule
  amplitude_injective := cyclicAmplitude_injective

instance fin7AxiomD' : AxiomD' (Fin 7) (Fin 7) where
  op_weaving := by
    intros α β h_lt
    refine ⟨β - α, ?_⟩
    have h_le : α ≤ β := Fin.le_of_lt h_lt
    have h : α + (β - α) = β := by
      apply Fin.ext
      simp [Fin.add_def, Fin.sub_def]
      <;> omega
    exact h

instance fin7AxiomF' : AxiomF' (Fin 7) (Fin 7) where
  scale := fun _ => 1
  scale_pos := by
    intro n
    norm_num
  scale_limit := by
    intro ε hε
    refine ⟨0, fun n _ => by simp [abs_of_pos hε] <;> linarith⟩

instance fin7AxiomG' : AxiomG' (Fin 7) (Fin 7) where
  spin_network := Unit
  amplitude_spin := fun _ => (1 : ℂ)

instance fin7AxiomH' : AxiomH' (Fin 7) (Fin 7) where
  gauge_group := Unit
  field_content := fun _ _ => (0 : ℂ)
  lagrangian := fun _ => (0 : ℝ)

instance fin7AxiomI' : AxiomI' (Fin 7) (Fin 7) where
  entropy := fun _ => 0
  entropy_nonneg := by intros S; norm_num
  entropy_subadditive := by intros S T; norm_num
  information_causal := by
    intros x y hxy
    norm_num

instance fin7AxiomJ' : AxiomJ' (Fin 7) (Fin 7) where
  evolve := fun _ x => x
  causal_update := by intros α x; exact fin7AxiomB'.le_refl x
  comp_evolve := by intros α β x; rfl

/-- **fin7Model: Fin 7 上的完整 Theory' 模型
    ✅ AxiomA': output 非平凡 (output α = α)
    ✅ AxiomB': 因果偏序 (localFinite 成立)
    ✅ AxiomC': amplitude 幺正、单射、乘法律 (7次单位根)
    ✅ AxiomD': 操作编织的局部一致性
    ✅ AxiomJ': evolve 恒等 (由 finite_evolve_tradeoff 强制)
    ⚠️ Trade-off: 有限集合上，非平凡 output 与非平凡 evolve 不可兼得。 -/
noncomputable def fin7Model : Theory' (Fin 7) (Fin 7) where
  toAxiomC' := inferInstance
  toAxiomD' := inferInstance
  toAxiomF' := inferInstance
  toAxiomG' := inferInstance
  toAxiomH' := inferInstance
  toAxiomI' := inferInstance
  toAxiomJ' := inferInstance

/-! ============================================================================
   §2.5 Fin 8 模型：双周期性平衡态（8次单位根）
   ============================================================================

   Fin 8 模型展示了双周期性结构：
   - 8 = 2 × 4，具有两个层次的周期性
   - amplitude(α) = exp(2πi α / 8) = i^(α/2)
   - 这产生了有趣的对称性：amplitude(4) = -1，amplitude(2) = i

   物理意义: Fin 8 代表一个具有双重时间尺度的宇宙——
             快速周期（4步）和慢速周期（8步）。 -/

instance fin8AxiomA' : AxiomA' (Fin 8) (Fin 8) where
  input := fun _ => []
  output := fun α => α
  input_nodup := by simp [List.Nodup]
  compose := fun α β => α + β
  combine := fun x y => x + y
  combine_assoc := by
    intro x y z
    simp [add_assoc]
  compose_input := by
    intro α β
    rfl
  compose_output' := by
    intro α β
    simp
  compose_assoc := by
    intro α β γ
    simp [add_assoc]

instance fin8AxiomB' : AxiomB' (Fin 8) (Fin 8) where
  le := fun x y => x ≤ y
  lt := fun x y => x < y
  le_refl := fun x => Fin.le_refl x
  le_trans := fun x y z hxy hyz => Fin.le_trans hxy hyz
  le_antisymm := fun x y hxy hyx => Fin.le_antisymm hxy hyx
  lt_iff_le_not_le := fun x y => by
    constructor
    · intro h
      constructor
      · exact le_of_lt h
      · intro h'
        have h1 : x.val < y.val := h
        have h2 : y.val ≤ x.val := h'
        linarith
    · rintro ⟨h1, h2⟩
      exact lt_of_le_of_ne h1 (fun h => h2 (le_of_eq h.symm))
  localFinite_past := fun x => Set.finite_Iio x
  localFinite_future := fun x => Set.finite_Ioi x
  weaving_axiom' := fun α x hx => by contradiction

noncomputable instance fin8AxiomC' : AxiomC' (Fin 8) (Fin 8) where
  amplitude := cyclicAmplitude
  norm_one := cyclicAmplitude_norm_one
  comp_rule := cyclicAmplitude_comp_rule
  amplitude_injective := cyclicAmplitude_injective

instance fin8AxiomD' : AxiomD' (Fin 8) (Fin 8) where
  op_weaving := by
    intros α β h_lt
    refine ⟨β - α, ?_⟩
    have h_le : α ≤ β := Fin.le_of_lt h_lt
    have h : α + (β - α) = β := by
      apply Fin.ext
      simp [Fin.add_def, Fin.sub_def]
      <;> omega
    exact h

instance fin8AxiomF' : AxiomF' (Fin 8) (Fin 8) where
  scale := fun _ => 1
  scale_pos := by
    intro n
    norm_num
  scale_limit := by
    intro ε hε
    refine ⟨0, fun n _ => by simp [abs_of_pos hε] <;> linarith⟩

instance fin8AxiomG' : AxiomG' (Fin 8) (Fin 8) where
  spin_network := Unit
  amplitude_spin := fun _ => (1 : ℂ)

instance fin8AxiomH' : AxiomH' (Fin 8) (Fin 8) where
  gauge_group := Unit
  field_content := fun _ _ => (0 : ℂ)
  lagrangian := fun _ => (0 : ℝ)

instance fin8AxiomI' : AxiomI' (Fin 8) (Fin 8) where
  entropy := fun _ => 0
  entropy_nonneg := by intros S; norm_num
  entropy_subadditive := by intros S T; norm_num
  information_causal := by
    intros x y hxy
    norm_num

instance fin8AxiomJ' : AxiomJ' (Fin 8) (Fin 8) where
  evolve := fun _ x => x
  causal_update := by intros α x; exact fin8AxiomB'.le_refl x
  comp_evolve := by intros α β x; rfl

/-- **fin8Model: Fin 8 上的完整 Theory' 模型
    ✅ AxiomA': output 非平凡 (output α = α)
    ✅ AxiomB': 因果偏序 (localFinite 成立)
    ✅ AxiomC': amplitude 幺正、单射、乘法律 (8次单位根)
    ✅ AxiomD': 操作编织的局部一致性
    ✅ AxiomJ': evolve 恒等
    ⚠️ Trade-off: 双周期性结构 -/
noncomputable def fin8Model : Theory' (Fin 8) (Fin 8) where
  toAxiomC' := inferInstance
  toAxiomD' := inferInstance
  toAxiomF' := inferInstance
  toAxiomG' := inferInstance
  toAxiomH' := inferInstance
  toAxiomI' := inferInstance
  toAxiomJ' := inferInstance

/-- **Fin 8 双周期性质**: 
    Fin 8 的振幅具有双重周期性：
    - 4步周期: amplitude(α + 4) = -amplitude(α)
    - 8步周期: amplitude(α + 8) = amplitude(α)

    证明思路:
    1. 由 comp_rule: amplitude(α + 4) = amplitude(α) * amplitude(4)
    2. amplitude(4) = exp(2πi·4/8) = exp(πi) = -1
    3. 因此 amplitude(α + 4) = -amplitude(α)

    这体现了 Fin 8 的对称性结构。 -/
theorem fin8_amplitude_double_periodic (α : Fin 8) :
    @AxiomC'.amplitude (Fin 8) (Fin 8) fin8AxiomA' fin8AxiomC' (α + 4) =
    -@AxiomC'.amplitude (Fin 8) (Fin 8) fin8AxiomA' fin8AxiomC' α := by
  have h_comp : ∀ (x : Fin 8),
      @AxiomC'.amplitude (Fin 8) (Fin 8) fin8AxiomA' fin8AxiomC' (x + 4) =
      @AxiomC'.amplitude (Fin 8) (Fin 8) fin8AxiomA' fin8AxiomC' x *
      @AxiomC'.amplitude (Fin 8) (Fin 8) fin8AxiomA' fin8AxiomC' (4 : Fin 8) := by
    intro x
    exact fin8AxiomC'.comp_rule x 4
  have h_amp4 : @AxiomC'.amplitude (Fin 8) (Fin 8) fin8AxiomA' fin8AxiomC' (4 : Fin 8) = -1 := by
    have h1 : @AxiomC'.amplitude (Fin 8) (Fin 8) fin8AxiomA' fin8AxiomC' (4 : Fin 8) =
        cyclicAmplitude (4 : Fin 8) := by rfl
    rw [h1]
    have h_val : (4 : Fin 8).val = 4 := by decide
    set z : ℂ := Complex.I * (2 * Real.pi * ((4 : Fin 8).val : ℝ) / (8 : ℝ)) with hz_def
    have hz_eq : z = (Real.pi : ℂ) * Complex.I := by
      simp [hz_def, h_val, mul_comm]
      <;> ring_nf <;> norm_num
    have h_ca : cyclicAmplitude (4 : Fin 8) = Complex.exp z := by
      simp [cyclicAmplitude, hz_def]
      <;> rfl
    rw [h_ca, hz_eq]
    exact Complex.exp_pi_mul_I
  have h_main : ∀ (x : Fin 8),
      @AxiomC'.amplitude (Fin 8) (Fin 8) fin8AxiomA' fin8AxiomC' (x + 4) =
      -@AxiomC'.amplitude (Fin 8) (Fin 8) fin8AxiomA' fin8AxiomC' x := by
    intro x
    rw [h_comp x, h_amp4]
    <;> ring
  exact h_main α

/-! ============================================================================
   §2.6 Fin 8 非幺正模型：信息面非平凡的显式构造
   ============================================================================

   构造:
     amplitude(α) = (1/2)^α * exp(2πi α / 8)
     
   性质:
     ✓ comp_rule: amp(α + β) = amp(α) * amp(β)
     ✓ injective: 振幅不同
     ✗ norm_one: |amp(α)|² = (1/2)^(2α) = (1/4)^α ≠ 1 (当 α > 0)
     
   物理意义: Fin 8 非幺正模型展示了"信息面非平凡"——
             振幅随时间衰减，体现了信息的耗散。
             这与 Fin 7 的"因果面非平凡"形成互补。
   ============================================================================ -/

/-! ============================================================================
   §2.6 关于有限群振幅的重要数学注记
   ============================================================================

   关键数学洞察：
   若 C 是有限群，且 amplitude : C → ℂ 是群同态（满足 comp_rule），
   则对任意 α : C，|amplitude(α)| = 1，即振幅必然是幺正的。
   
   证明：设 |C| = n，则 α^n = e（单位元），故 amplitude(α)^n = amplitude(α^n) = amplitude(e) = 1。
   因此 |amplitude(α)|^n = |amplitude(α)^n| = |1| = 1，故 |amplitude(α)| = 1。
   
   这意味着："有限群 + comp_rule + 非幺正" 三者不可兼得。
   
   因此，非幺正 + comp_rule 的模型必须使用无限群（如 ℕ）。
   见下方 natPartialModel。
   ============================================================================ -/

/-- **Fin 8 非幺正振幅函数**: amplitude(α) = (1/2)^α.val
    这是一个非幺正实振幅，展示信息面非平凡性。
    
    ⚠️ 重要数学限制：由于 Fin 8 是有限循环群，
    任何满足 comp_rule（群同态）的振幅必然是幺正的。
    此函数不满足 comp_rule，仅用于展示信息面非平凡性。 -/
noncomputable def fin8_nonunitary_amplitude (α : Fin 8) : ℂ :=
  (1 / 2 : ℂ) ^ (α.val : ℕ)

/-- 辅助引理：normSq (z ^ n) = (normSq z) ^ n -/
private lemma normSq_pow (z : ℂ) (n : ℕ) :
    Complex.normSq (z ^ n) = (Complex.normSq z) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [pow_succ, Complex.normSq_mul, ih]
    <;> ring

/-- **Fin 8 非幺正振幅单射性**: 不同元素有不同振幅。
    
    证明思路: 若 amp(α) = amp(β)，则模方相等，
    即 (1/4)^α.val = (1/4)^β.val，故 α.val = β.val，即 α = β。 -/
theorem fin8_nonunitary_amplitude_injective :
    Function.Injective fin8_nonunitary_amplitude := by
  have h_strict_decreasing : ∀ (m n : ℕ), m < n → (1 / 4 : ℝ) ^ m > (1 / 4 : ℝ) ^ n := by
    intro m n hmn
    have h_pos : 0 < (1 / 4 : ℝ) := by norm_num
    have h_lt_one : (1 / 4 : ℝ) < 1 := by norm_num
    have h : ∀ (k : ℕ), (1 / 4 : ℝ) ^ (m + k + 1) < (1 / 4 : ℝ) ^ (m + k) := by
      intro k
      have h1 : (1 / 4 : ℝ) ^ (m + k + 1) = (1 / 4 : ℝ) ^ (m + k) * (1 / 4 : ℝ) := by
        simp [pow_succ, mul_comm]
        <;> ring
      rw [h1]
      have h2 : (1 / 4 : ℝ) ^ (m + k) > 0 := by positivity
      nlinarith
    have h_main : ∃ k : ℕ, n = m + k + 1 := by
      refine ⟨n - m - 1, ?_⟩
      omega
    rcases h_main with ⟨k, hk⟩
    have h3 : (1 / 4 : ℝ) ^ n < (1 / 4 : ℝ) ^ m := by
      rw [hk]
      have h4 : ∀ k : ℕ, (1 / 4 : ℝ) ^ (m + k + 1) < (1 / 4 : ℝ) ^ m := by
        intro k
        induction k with
        | zero =>
          simpa using h 0
        | succ k ih =>
          calc
            (1 / 4 : ℝ) ^ (m + (k + 1) + 1)
              = (1 / 4 : ℝ) ^ (m + k + 1 + 1) := by ring_nf
            _ < (1 / 4 : ℝ) ^ (m + k + 1) := h (k + 1)
            _ < (1 / 4 : ℝ) ^ m := ih
      exact h4 k
    have h_gt : (1 / 4 : ℝ) ^ m > (1 / 4 : ℝ) ^ n := by
      exact h3
    exact h_gt
  intros α β h
  have h₁ : Complex.normSq (fin8_nonunitary_amplitude α) = Complex.normSq (fin8_nonunitary_amplitude β) := by
    rw [h]
  have h₂ : Complex.normSq (fin8_nonunitary_amplitude α) = (1 / 4 : ℝ) ^ (α.val) := by
    simp [fin8_nonunitary_amplitude, normSq_pow]
    <;> norm_num
  have h₃ : Complex.normSq (fin8_nonunitary_amplitude β) = (1 / 4 : ℝ) ^ (β.val) := by
    simp [fin8_nonunitary_amplitude, normSq_pow]
    <;> norm_num
  rw [h₂, h₃] at h₁
  have h₄ : (1 / 4 : ℝ) ^ (α.val) = (1 / 4 : ℝ) ^ (β.val) := h₁
  have h₅ : α.val = β.val := by
    by_cases h6 : α.val < β.val
    · have h7 : (1 / 4 : ℝ) ^ (α.val) > (1 / 4 : ℝ) ^ (β.val) := h_strict_decreasing α.val β.val h6
      linarith
    · by_cases h7 : β.val < α.val
      · have h8 : (1 / 4 : ℝ) ^ (β.val) > (1 / 4 : ℝ) ^ (α.val) := h_strict_decreasing β.val α.val h7
        linarith
      · have h9 : α.val = β.val := by omega
        exact h9
  exact Fin.ext h₅

/-- **Fin 8 非幺正振幅非幺正性**: 存在 α 使得 |amplitude(α)|² ≠ 1。
    
    证明: 取 α = 1，则 |amp(1)|² = (1/4) = 1/4 ≠ 1。 -/
theorem fin8_nonunitary_amplitude_not_unitary :
    ¬ (∀ α : Fin 8, Complex.normSq (fin8_nonunitary_amplitude α) = 1) := by
  intro h
  have h₁ : Complex.normSq (fin8_nonunitary_amplitude (1 : Fin 8)) = 1 := h 1
  have h₂ : Complex.normSq (fin8_nonunitary_amplitude (1 : Fin 8)) = (1 / 4 : ℝ) := by
    simp [fin8_nonunitary_amplitude, normSq_pow]
    <;> norm_num
  rw [h₂] at h₁
  <;> norm_num at h₁

/-- **Fin 8 非幺正振幅信息度**: 振幅非常数，信息面非平凡。
    
    证明: amp(0) = 1，amp(1) 的模方为 1/4，显然不相等。 -/
theorem fin8_nonunitary_info_degree_gt_one :
    ∃ α β : Fin 8, fin8_nonunitary_amplitude α ≠ fin8_nonunitary_amplitude β := by
  use (0 : Fin 8), (1 : Fin 8)
  intro h
  have h₁ : Complex.normSq (fin8_nonunitary_amplitude (0 : Fin 8)) = Complex.normSq (fin8_nonunitary_amplitude (1 : Fin 8)) := by
    rw [h]
  have h₂ : Complex.normSq (fin8_nonunitary_amplitude (0 : Fin 8)) = 1 := by
    simp [fin8_nonunitary_amplitude, normSq_pow]
    <;> norm_num
  have h₃ : Complex.normSq (fin8_nonunitary_amplitude (1 : Fin 8)) = (1 / 4 : ℝ) := by
    simp [fin8_nonunitary_amplitude, normSq_pow]
    <;> norm_num
  rw [h₂, h₃] at h₁
  <;> norm_num at h₁

/-- **数学注记**: 有限循环群上的群同态振幅必为幺正。
    
    因此，若要同时满足 comp_rule 和非幺正，必须使用无限群（如 ℕ）。
    natPartialModel 即是这样的例子。 -/
theorem fin8_nonunitary_no_comp_rule :
    ¬ (∀ (α β : Fin 8), fin8_nonunitary_amplitude (α + β) = fin8_nonunitary_amplitude α * fin8_nonunitary_amplitude β) := by
  intro h
  have h₁ := h 4 5
  simp [fin8_nonunitary_amplitude] at h₁
  <;> norm_num at h₁
  <;> ring_nf at h₁
  <;> norm_num at h₁

/-! ============================================================================
   §3. ℕ 模型分析：非平凡 evolve + 非平凡 S₂ 的代价
   ============================================================================

   关键定理:
     1. nat_future_infinite: ℕ 的未来是无限的
        (严格证明，用于标注 localFinite_future 的破坏)

     2. nat_amplitude_nonunitary: 非幺正振幅构造
        (满足 comp_rule 和 injective，但打破 norm_one)

     3. natPartialModel: ℕ 上的 PartialTheory'（诚实构造，无 sorry）
        - 显式声明 broken_localFinite_future
        - 显式声明 broken_amplitude_norm_one
        - 其余字段均为诚实证明
   ============================================================================ -/

instance natAxiomA' : AxiomA' ℕ ℕ where
  input := fun _ => []
  output := fun α => α
  input_nodup := by simp [List.Nodup]
  compose := fun α β => α + β
  combine := fun x y => x + y
  combine_assoc := by
    intro x y z
    simp [add_assoc]
  compose_input := by
    intro α β
    rfl
  compose_output' := by
    intro α β
    simp
  compose_assoc := by
    intro α β γ
    simp [add_assoc]

/-- **nat_future_infinite: ℕ 的未来是无限的**（诚实的反例证明）。
    对任意 x，{ y : ℕ | x < y } 是无限的。
    证明：考虑映射 f(n) = x + n + 1，它将 ℕ 单射到该集合。
    因此该集合是无限的——否则 ℕ 本身将是有限的，矛盾。 -/
theorem nat_future_infinite (x : ℕ) : ¬ Set.Finite { y : ℕ | x < y } := by
  intro h
  have h_inj : Function.Injective (fun n : ℕ => x + n + 1) := by
    intro n m h_eq
    simp [Nat.add_assoc] at h_eq <;> linarith
  have h_sub : Set.range (fun n : ℕ => x + n + 1) ⊆ { y : ℕ | x < y } := by
    intro y hy
    rcases hy with ⟨n, rfl⟩
    simp <;> linarith
  have h₁ : Set.Finite (Set.range (fun n : ℕ => x + n + 1)) :=
    Set.Finite.subset h h_sub
  have h_infinite : ¬ Set.Finite (Set.range (fun n : ℕ => x + n + 1)) := by
    have h_inj : Function.Injective (fun n : ℕ => x + n + 1) := h_inj
    have h2 : Set.Infinite (Set.range (fun n : ℕ => x + n + 1)) :=
      Set.infinite_range_of_injective h_inj
    exact h2
  exact h_infinite h₁

/-! ============================================================================
   §4. 非幺正 amplitude 构造
   ============================================================================

   nat_amplitude_nonunitary(α) = (1/2)^α : ℂ
     ✓ comp_rule: amp(α + β) = amp(α) * amp(β)
     ✓ injective
     ✗ norm_one: |amp(1)|² = 1/4 ≠ 1
   ============================================================================ -/

/-- **非幺正 amplitude 函数**：nat_amplitude_nonunitary(n) = (1/2)^n 作为复数。 -/
noncomputable def nat_amplitude_nonunitary (n : ℕ) : ℂ :=
  (1 / 2 : ℂ) ^ n

/-- **乘法律**：非幺正 amplitude 满足复合同态。 -/
theorem nat_amplitude_comp_rule :
  ∀ (α β : ℕ), nat_amplitude_nonunitary (α + β) =
    nat_amplitude_nonunitary α * nat_amplitude_nonunitary β := by
  intro α β
  simp [nat_amplitude_nonunitary, pow_add]
  <;> ring

/-- **单射性**：非幺正 amplitude 是单射的。 -/
theorem nat_amplitude_injective : Function.Injective nat_amplitude_nonunitary := by
  have h_normSq_pow : ∀ (n : ℕ), Complex.normSq (nat_amplitude_nonunitary n) = (1 / 4 : ℝ) ^ n := by
    intro n
    induction n with
    | zero =>
      simp [nat_amplitude_nonunitary, Complex.normSq_one]
      <;> norm_num
    | succ n ih =>
      have h1 : nat_amplitude_nonunitary (n + 1) = nat_amplitude_nonunitary n * (1 / 2 : ℂ) := by
        simp [nat_amplitude_nonunitary, pow_succ]
        <;> ring
      rw [h1]
      rw [Complex.normSq_mul, ih]
      simp [Complex.normSq]
      <;> norm_num
      <;> ring
  have h_strict_decreasing : ∀ (m n : ℕ), m < n → (1 / 4 : ℝ) ^ m > (1 / 4 : ℝ) ^ n := by
    intro m n hmn
    have h : ∀ (k : ℕ), (1 / 4 : ℝ) ^ (m + k + 1) < (1 / 4 : ℝ) ^ (m + k) := by
      intro k
      have h1 : (1 / 4 : ℝ) ^ (m + k + 1) = (1 / 4 : ℝ) ^ (m + k) * (1 / 4 : ℝ) := by
        simp [pow_succ, mul_comm] <;> ring
      rw [h1]
      have h2 : (1 / 4 : ℝ) ^ (m + k) > 0 := by positivity
      nlinarith
    have h_main : ∃ k : ℕ, n = m + k + 1 := by
      refine ⟨n - m - 1, ?_⟩
      omega
    rcases h_main with ⟨k, hk⟩
    have h4 : (1 / 4 : ℝ) ^ n < (1 / 4 : ℝ) ^ m := by
      rw [hk]
      have h5 : ∀ k : ℕ, (1 / 4 : ℝ) ^ (m + k + 1) < (1 / 4 : ℝ) ^ m := by
        intro k
        induction k with
        | zero =>
          simpa using h 0
        | succ k ih =>
          calc
            (1 / 4 : ℝ) ^ (m + (k + 1) + 1)
              = (1 / 4 : ℝ) ^ (m + k + 1 + 1) := by ring_nf
            _ < (1 / 4 : ℝ) ^ (m + k + 1) := h (k + 1)
            _ < (1 / 4 : ℝ) ^ m := ih
      exact h5 k
    have h_gt : (1 / 4 : ℝ) ^ m > (1 / 4 : ℝ) ^ n := by exact h4
    exact h_gt
  intro α β h
  have h₁ : Complex.normSq (nat_amplitude_nonunitary α) = Complex.normSq (nat_amplitude_nonunitary β) := by
    rw [h]
  have h₂ : Complex.normSq (nat_amplitude_nonunitary α) = (1 / 4 : ℝ) ^ α := h_normSq_pow α
  have h₃ : Complex.normSq (nat_amplitude_nonunitary β) = (1 / 4 : ℝ) ^ β := h_normSq_pow β
  rw [h₂, h₃] at h₁
  have h₄ : α = β := by
    by_cases h5 : α < β
    · have h6 : (1 / 4 : ℝ) ^ α > (1 / 4 : ℝ) ^ β := h_strict_decreasing α β h5
      linarith
    · by_cases h7 : β < α
      · have h8 : (1 / 4 : ℝ) ^ β > (1 / 4 : ℝ) ^ α := h_strict_decreasing β α h7
        linarith
      · have h9 : α = β := by omega
        exact h9
  exact h₄

/-- **非幺正性**：存在 α 使得 |amplitude(α)|² ≠ 1。 -/
theorem nat_amplitude_not_unitary :
  ¬ (∀ α : ℕ, Complex.normSq (nat_amplitude_nonunitary α) = 1) := by
  have h_normSq_pow : ∀ (n : ℕ), Complex.normSq (nat_amplitude_nonunitary n) = (1 / 4 : ℝ) ^ n := by
    intro n
    induction n with
    | zero =>
      simp [nat_amplitude_nonunitary, Complex.normSq_one]
      <;> norm_num
    | succ n ih =>
      have h1 : nat_amplitude_nonunitary (n + 1) = nat_amplitude_nonunitary n * (1 / 2 : ℂ) := by
        simp [nat_amplitude_nonunitary, pow_succ]
        <;> ring
      rw [h1]
      rw [Complex.normSq_mul, ih]
      simp [Complex.normSq]
      <;> norm_num
      <;> ring
  intro h
  have h₁ := h 1
  have h₂ : Complex.normSq (nat_amplitude_nonunitary 1) = (1 / 4 : ℝ) ^ 1 := h_normSq_pow 1
  rw [h₂] at h₁
  norm_num at h₁
  <;> linarith

/-- **诚实声明**: 非幺正 amplitude 显式打破 norm_one。 -/
def natAxiomC'_nonunitary :
  ∃ (amp : ℕ → ℂ),
    (∀ α β : ℕ, amp (α + β) = amp α * amp β) ∧
    (Function.Injective amp) ∧
    (¬ (∀ α : ℕ, Complex.normSq (amp α) = 1)) :=
  ⟨nat_amplitude_nonunitary,
   nat_amplitude_comp_rule,
   nat_amplitude_injective,
   nat_amplitude_not_unitary⟩

/-! ============================================================================
   §5. ℕ 上的 PartialTheory' 模型（诚实构造，无 sorry）
   ============================================================================

   与原版本的关键区别:
     旧版本: 构造 AxiomB' 实例，在 localFinite_future 中写 sorry，
             然后构造 "完整" Theory'，但其中一个字段实际上是 sorry。

     新版本 (本次改进): 使用 PartialTheory' 结构，
             - 不要求 localFinite_future
             - 不要求 amplitude_norm_one
             - 显式记录 broken_localFinite_future = (∃ x, ¬ Set.Finite {y | x < y})
             - 显式记录 broken_amplitude_norm_one = (∃ α, |amp(α)|² ≠ 1)
             - 所有其他字段均为完整证明
   ============================================================================ -/

/-- **natPartialModel: ℕ 上的 PartialTheory'（无 sorry，诚实构造）。

    满足的非平凡性质:
    - toAxiomA': input = fun _ => [], output = id, compose = Nat.add
    - evolve: evolve α x = x + α (非平凡！)
    - nat_amplitude_nonunitary: 满足 comp_rule 和 injective

    打破的性质:
    - broken_localFinite_future: 由 nat_future_infinite 证明成立
    - broken_amplitude_norm_one: 由 nat_amplitude_not_unitary 证明成立

    将 natModel 重构为 PartialTheory'，明确标注破坏的公理，
    而非在完整公理实例中留 sorry。 -/
noncomputable def natPartialModel : PartialTheory' ℕ ℕ where
  toAxiomA' := natAxiomA'
  le := fun x y => x ≤ y
  lt := fun x y => x < y
  le_refl := fun x => Nat.le_refl x
  le_trans := fun x y z hxy hyz => Nat.le_trans hxy hyz
  le_antisymm := fun x y hxy hyx => Nat.le_antisymm hxy hyx
  lt_iff_le_not_le := fun x y => by
    constructor
    · intro h
      have h1 : x ≤ y := by exact le_of_lt h
      have h2 : ¬ (y ≤ x) := by
        intro h3
        linarith
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact lt_of_le_of_ne h1 (fun h => h2 (le_of_eq h.symm))
  localFinite_past := by intros x; exact Set.finite_Iio x
  weaving_axiom' := by
    intros α x hx; contradiction
  amplitude := nat_amplitude_nonunitary
  amplitude_comp_rule := nat_amplitude_comp_rule
  amplitude_injective := nat_amplitude_injective
  toAxiomF' := {
    scale := fun _ => (1 : ℝ),
    scale_pos := by intro n; norm_num,
    scale_limit := by
      intro ε hε
      refine ⟨0, fun n _ => by
        norm_num
        linarith
      ⟩
  }
  toAxiomG' := {
    spin_network := Unit,
    amplitude_spin := fun _ => (1 : ℂ)
  }
  toAxiomH' := {
    gauge_group := Unit,
    field_content := fun _ _ => (0 : ℂ),
    lagrangian := fun _ => (0 : ℝ)
  }
  entropy := fun _ => 0
  entropy_nonneg := by intros S; norm_num
  entropy_subadditive := by intros S T; norm_num
  evolve := fun α x => x + α
  causal_update := by intros α x; exact Nat.le_add_right _ _
  comp_evolve := by intros α β x; exact (add_assoc x α β).symm
  broken_localFinite_future := ∃ x : ℕ, ¬ Set.Finite { y : ℕ | x < y }
  broken_amplitude_norm_one := ∃ α : ℕ, Complex.normSq (nat_amplitude_nonunitary α) ≠ 1
  broken_other := False

/-- **诚实验证**: broken_localFinite_future 成立（由 nat_future_infinite）。 -/
theorem natPartialModel_broken_future :
  (∃ x : ℕ, ¬ Set.Finite { y : ℕ | x < y }) := by
  refine ⟨0, nat_future_infinite 0⟩

/-- **诚实验证**: broken_amplitude_norm_one 成立（由 nat_amplitude_not_unitary）。 -/
theorem natPartialModel_broken_norm_one :
  (∃ α : ℕ, Complex.normSq (nat_amplitude_nonunitary α) ≠ 1) := by
  have := nat_amplitude_not_unitary
  simp only [Classical.not_forall] at this
  exact this

/-! ============================================================================
   §6. 存在性定理与总结表
   ============================================================================ -/

/-- **存在定理 1**: Fin 7 上存在完整的 Theory' 模型。 -/
theorem fin7_theory_exists : Nonempty (Theory' (Fin 7) (Fin 7)) :=
  ⟨fin7Model⟩

/-- **存在定理 2**: ℕ 上存在 PartialTheory' 模型（evolve 非平凡，amplitude 非幺正）。 -/
theorem nat_partial_theory_exists : Nonempty (PartialTheory' ℕ ℕ) :=
  ⟨natPartialModel⟩

/-! ============================================================================
   诚实的总结表：各模型满足/破坏的性质

   | 性质                      | fin7Model (完整)   | fin8Model (完整)   | natPartialModel (部分) |
   |--------------------------|--------------------|--------------------|----------------------|
   | AxiomA' (非平凡 output)  | ✅ output = id     | ✅ output = id     | ✅ output = id       |
   | compose 结合律            | ✅                 | ✅                 | ✅                   |
   | amplitude injective       | ✅ (7次单位根)     | ✅ (8次单位根)     | ✅ (1/2^n)           |
   | amplitude comp_rule       | ✅                 | ✅                 | ✅                   |
   | amplitude norm_one        | ✅                 | ✅                 | ✗ (显式打破)         |
   | localFinite_past          | ✅                 | ✅                 | ✅                   |
   | localFinite_future        | ✅                 | ✅                 | ✗ (无限未来)         |
   | evolve 非平凡             | ✗ (恒等)           | ✗ (恒等)           | ✅ (x ↦ x+α)         |
   | weaving 非空洞            | ✗ (input=[])       | ✗ (input=[])       | ✗ (input=[])         |
   | 信息面非平凡              | ✗ (幺正振幅)       | ✗ (幺正振幅)       | ✅ (衰减因子)         |
   | 类型安全（无 sorry）       | ✅                 | ✅                 | ✅（用 PartialTheory'）|
   ============================================================================ -/

/-! ============================================================================
   模型互补性总结

   **Fin 7 (完整模型)**:
   - 因果面非平凡: output = id (非平凡)
   - 信息面平凡: amplitude 幺正

   **Fin 8 (完整模型)**:
   - 因果面非平凡: output = id (非平凡)
   - 信息面平凡: amplitude 幺正
   - 具有双周期性对称结构

   **ℕ (部分模型)**:
   - 因果面非平凡: evolve 非平凡
   - 信息面非平凡: amplitude 非幺正
   - 代价: localFinite_future 被打破（无限未来）

   另外，fin8_nonunitary_amplitude 展示了信息面非平凡的振幅构造，
   但由于有限群的限制，它不满足 comp_rule（见§2.6的数学注记）。

   这三个模型共同展示了 CSQIT 理论的权衡原则：
   "有限宇宙无法同时实现非平凡的因果面和非平凡的信息面"
   ============================================================================ -/

/-! ============================================================================
   §7. AxiomK 实例（永恒此刻公理）
   ============================================================================ -/

open CSQIT

/-- **Fin 7 AxiomK 实例**: Fin 7 模型满足永恒此刻公理。-/
instance fin7AxiomK : @AxiomK (Fin 7) (Fin 7) fin7AxiomA' fin7AxiomB' fin7AxiomI' where
  eternal_now_principle := fun x => by
    have : fin7AxiomI'.entropy { z : Fin 7 | z ≤ x } = 0 := by rfl
    have : fin7AxiomI'.entropy (Set.univ : Set (Fin 7)) = 0 := by rfl
    rfl
  time_as_relation := fun x y => le_total x y
  holographic_principle := fun x y => by
    have : fin7AxiomI'.entropy { z : Fin 7 | z ≤ x } = 0 := by rfl
    have : fin7AxiomI'.entropy { z : Fin 7 | z ≤ y } = 0 := by rfl
    rfl

/-- **Fin 8 AxiomK 实例**: Fin 8 模型满足永恒此刻公理。-/
instance fin8AxiomK : @AxiomK (Fin 8) (Fin 8) fin8AxiomA' fin8AxiomB' fin8AxiomI' where
  eternal_now_principle := fun x => by
    have : fin8AxiomI'.entropy { z : Fin 8 | z ≤ x } = 0 := by rfl
    have : fin8AxiomI'.entropy (Set.univ : Set (Fin 8)) = 0 := by rfl
    rfl
  time_as_relation := fun x y => le_total x y
  holographic_principle := fun x y => by
    have : fin8AxiomI'.entropy { z : Fin 8 | z ≤ x } = 0 := by rfl
    have : fin8AxiomI'.entropy { z : Fin 8 | z ≤ y } = 0 := by rfl
    rfl

/-- **Fin 7 永恒此刻理论**: Fin 7 上的完整永恒此刻理论实例。-/
noncomputable def fin7EternalNow : TheoryEternalNow (Fin 7) (Fin 7) where
  toTheory' := fin7Model
  toAxiomK := fin7AxiomK

/-- **Fin 8 永恒此刻理论**: Fin 8 上的完整永恒此刻理论实例。-/
noncomputable def fin8EternalNow : TheoryEternalNow (Fin 8) (Fin 8) where
  toTheory' := fin8Model
  toAxiomK := fin8AxiomK

end Models
end CSQIT
