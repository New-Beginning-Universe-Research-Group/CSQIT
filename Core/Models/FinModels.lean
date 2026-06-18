/-
CSQIT 10.4.5 核心模块 - 非平凡有限模型
文件: Core/Models/FinModels.lean
版本: 10.4.5 (Canonical Textbook Edition)

================================================================================
模块概述
================================================================================

本文件显式构造 CSQIT 理论的一个非平凡有限模型：
  M = Fin 5   （5 个关系元，具有 0 < 1 < 2 < 3 < 4 的标准全序）
  C = Fin 4   （4 个规则，具有加法群结构和 4 次单位根振幅表示）

关键非平凡性：
1. M 上存在真实的因果序（0 < 1 < 2 < 3 < 4）
2. C 上有非平凡的群运算（加法 mod 4）
3. 振幅函数 amplitude(n) = i^n 是单射且保持乘法
4. 虽然 input_must_be_empty 强制所有 input = []，
   但 M、C、振幅、因果序都非平凡

这证明 CSQIT 公理体系在受限条件下仍能容纳丰富结构。

================================================================================
已证明的结论
================================================================================
- nonTrivialFinModel : Theory (Fin 5) (Fin 4)      （完整模型实例）
- Theory 在 M = Fin 5, C = Fin 4 下非空               （模块存在性）

================================================================================
依赖说明
================================================================================
本文件需要 Axioms.lean 中定义的公理结构。
它不依赖 Theorems.lean 中的 input_must_be_empty，
而是在模型定义中显式选择 input _ := [] 来满足 AxiomA。
-/

import Core.Axioms
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace CSQIT.Models.FinModel5x4

open CSQIT

/-! ============================================================================
   §1 辅助定义与引理（关于 4 次单位根和 Fin 4 加法）
   ============================================================================ -/

private lemma I_pow_0 : Complex.I ^ (0 : ℕ) = (1 : ℂ) := by simp
private lemma I_pow_1 : Complex.I ^ (1 : ℕ) = Complex.I := by simp
private lemma I_pow_2 : Complex.I ^ 2 = -1 := by
  simp [pow_two, Complex.I_mul_I] <;> ring
private lemma I_pow_3 : Complex.I ^ 3 = -Complex.I := by
  have h : Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by
    simp [pow_succ] <;> ring
  rw [h, I_pow_2] <;> ring
private lemma I_pow_4 : Complex.I ^ 4 = 1 := by
  have h : Complex.I ^ 4 = Complex.I ^ 3 * Complex.I := by
    simp [pow_succ] <;> ring
  rw [h, I_pow_3] <;> simp <;> ring

/-- 辅助引理：证明 I^n 在 {0,1,2,3} 时两两不相等

这些具体的不等式用于 h_nm 引理。-/
private lemma I_neq_1 : Complex.I ≠ (1 : ℂ) := by
  intro h; have := congr_arg (fun z : ℂ => z.re) h; simp at this

private lemma I_neq_neg1 : Complex.I ≠ (-1 : ℂ) := by
  intro h; have := congr_arg (fun z : ℂ => z.im) h; simp at this

private lemma I_neq_negI : Complex.I ≠ (-Complex.I : ℂ) := by
  intro h
  have h1 : Complex.I.im = (-Complex.I).im := congr_arg Complex.im h
  simp only [Complex.I, Complex.neg_im] at h1
  have h_pos : (1 : ℝ) > 0 := by norm_num
  have h_neg : (-1 : ℝ) < 0 := by norm_num
  exact absurd h1 (by linarith)

/-- 实数 1 ≠ -1 的引理 -/
private lemma one_ne_neg1 : (1 : ℂ) ≠ -1 := by
  intro h
  have h1 : (1 : ℂ).re = (-1 : ℂ).re := congr_arg Complex.re h
  simp at h1
  have h_pos : (1 : ℝ) > 0 := by norm_num
  have h_neg : (-1 : ℝ) < 0 := by norm_num
  exact absurd h1 (by linarith)

/-- 1 ≠ -Complex.I 的引理 -/
private lemma one_ne_negI : (1 : ℂ) ≠ -Complex.I := by
  intro h; have := congr_arg (fun z : ℂ => z.re) h; simp at this

private lemma neg1_neq_I : (-1 : ℂ) ≠ Complex.I := by
  intro h; exact I_neq_neg1 h.symm

private lemma neg1_neq_negI : (-1 : ℂ) ≠ (-Complex.I : ℂ) := by
  intro h; have := congr_arg (fun z : ℂ => z.im) h; simp at this

private lemma negI_neq_I : (-Complex.I : ℂ) ≠ Complex.I := by
  intro h; exact I_neq_negI h.symm

/-- 辅助引理：从 I^n = I^m（当 n,m ∈ {0,1,2,3}）推出 n = m

证明：直接展开 I^n 和 I^m 的具体值，利用这些值互不相等的事实证明 n=m。
关键洞察：若 I^n = I^m 但 n≠m，则会导出复数单位之间不可能的相等关系（如 1 = I）。

我们先在假设 h 上应用 rw 来建立矛盾等式，然后用 I_neq_* 引理配合 absurd 证明 False。-/
private lemma h_nm (n m : ℕ) (h : Complex.I ^ n = Complex.I ^ m)
    (hn : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3)
    (hm : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) : n = m := by
  cases hn with
  | inl hn0 =>
    cases hm with
    | inl hm0 => rw [hn0, hm0]
    | inr hm' => cases hm' with
      | inl hm1 =>
        -- n=0, m=1：若 I^0 = I^1 则 1 = I，矛盾
        have contra := calc
          Complex.I = Complex.I ^ 1 := by rw [I_pow_1]
          _ = Complex.I ^ 0 := by { rw [hn0, hm1] at h; exact h.symm }
          _ = 1 := by rw [I_pow_0]
        exact absurd contra I_neq_1
      | inr hm'' => cases hm'' with
        | inl hm2 =>
          -- n=0, m=2：若 I^0 = I^2 则 1 = -1，矛盾
          have contra := calc
            (-1 : ℂ) = Complex.I ^ 2 := by rw [I_pow_2]
            _ = Complex.I ^ 0 := by
              rw [hn0, hm2] at h
              exact h.symm
            _ = 1 := by rw [I_pow_0]
          exact absurd contra one_ne_neg1.symm
        | inr hm3 =>
          -- n=0, m=3：若 I^0 = I^3 则 1 = -I，矛盾
          have contra := calc
            (-Complex.I : ℂ) = Complex.I ^ 3 := by rw [I_pow_3]
            _ = Complex.I ^ 0 := by
              rw [hn0, hm3] at h
              exact h.symm
            _ = 1 := by rw [I_pow_0]
          exact absurd contra one_ne_negI.symm
  | inr hn' => cases hn' with
    | inl hn1 =>
      cases hm with
      | inl hm0 =>
        -- n=1, m=0：若 I^1 = I^0 则 I = 1，矛盾
        have contra := calc
          Complex.I = Complex.I ^ 1 := by rw [I_pow_1]
          _ = Complex.I ^ 0 := by { rw [hn1, hm0] at h; exact h }
          _ = 1 := by rw [I_pow_0]
        exact absurd contra I_neq_1
      | inr hm' => cases hm' with
        | inl hm1 => rw [hn1, hm1]
        | inr hm'' => cases hm'' with
          | inl hm2 =>
            -- n=1, m=2：若 I^1 = I^2 则 I = -1，矛盾
            have contra := calc
              Complex.I = Complex.I ^ 1 := by rw [I_pow_1]
              _ = Complex.I ^ 2 := by { rw [hn1, hm2] at h; exact h }
              _ = -1 := by rw [I_pow_2]
            exact absurd contra I_neq_neg1
          | inr hm3 =>
            -- n=1, m=3：若 I^1 = I^3 则 I = -I，矛盾
            have contra := calc
              Complex.I = Complex.I ^ 1 := by rw [I_pow_1]
              _ = Complex.I ^ 3 := by { rw [hn1, hm3] at h; exact h }
              _ = -Complex.I := by rw [I_pow_3]
            exact absurd contra I_neq_negI
    | inr hn'' => cases hn'' with
      | inl hn2 =>
        cases hm with
        | inl hm0 =>
          -- n=2, m=0：若 I^2 = I^0 则 -1 = 1，矛盾
          have contra := calc
            (-1 : ℂ) = Complex.I ^ 2 := by rw [I_pow_2]
            _ = Complex.I ^ 0 := by { rw [hn2, hm0] at h; exact h }
            _ = 1 := by rw [I_pow_0]
          exact absurd contra one_ne_neg1.symm
        | inr hm' => cases hm' with
          | inl hm1 =>
            -- n=2, m=1：若 I^2 = I^1 则 -1 = I，矛盾
            have contra := calc
              (-1 : ℂ) = Complex.I ^ 2 := by rw [I_pow_2]
              _ = Complex.I ^ 1 := by { rw [hn2, hm1] at h; exact h }
              _ = Complex.I := by rw [I_pow_1]
            exact absurd contra neg1_neq_I
          | inr hm'' => cases hm'' with
            | inl hm2 => rw [hn2, hm2]
            | inr hm3 =>
              -- n=2, m=3：若 I^2 = I^3 则 -1 = -I，矛盾
              have contra := calc
                (-1 : ℂ) = Complex.I ^ 2 := by rw [I_pow_2]
                _ = Complex.I ^ 3 := by { rw [hn2, hm3] at h; exact h }
                _ = -Complex.I := by rw [I_pow_3]
              exact absurd contra neg1_neq_negI
      | inr hn3 =>
        cases hm with
        | inl hm0 =>
          -- n=3, m=0：若 I^3 = I^0 则 -I = 1，矛盾
          have contra := calc
            (-Complex.I : ℂ) = Complex.I ^ 3 := by rw [I_pow_3]
            _ = Complex.I ^ 0 := by { rw [hn3, hm0] at h; exact h }
            _ = 1 := by rw [I_pow_0]
          exact absurd contra one_ne_negI.symm
        | inr hm' => cases hm' with
          | inl hm1 =>
            -- n=3, m=1：若 I^3 = I^1 则 -I = I，矛盾
            have contra := calc
              (-Complex.I : ℂ) = Complex.I ^ 3 := by rw [I_pow_3]
              _ = Complex.I ^ 1 := by { rw [hn3, hm1] at h; exact h }
              _ = Complex.I := by rw [I_pow_1]
            exact absurd contra negI_neq_I
          | inr hm'' => cases hm'' with
            | inl hm2 =>
              -- n=3, m=2：若 I^3 = I^2 则 -I = -1，矛盾
              have contra := calc
                (-Complex.I : ℂ) = Complex.I ^ 3 := by rw [I_pow_3]
                _ = Complex.I ^ 2 := by { rw [hn3, hm2] at h; exact h }
                _ = -1 := by rw [I_pow_2]
              exact absurd contra neg1_neq_negI.symm
            | inr hm3 => rw [hn3, hm3]

/-- 振幅的乘法性：i^(m+n) = i^m * i^n（在 Fin 4 的模运算下）-/
private theorem fin4_I_pow_add (m n : Fin 4) :
    Complex.I ^ ((m + n).val) = (Complex.I ^ (m.val)) * (Complex.I ^ (n.val)) := by
  let a := m.val
  let b := n.val
  have ha : a < 4 := Fin.is_lt m
  have hb : b < 4 := Fin.is_lt n
  have h_main : ∀ (a b : ℕ), a < 4 → b < 4 →
      Complex.I ^ ((a + b) % 4) = (Complex.I ^ a) * (Complex.I ^ b) := by
    intro a' b' ha' hb'
    have ha'' : a' = 0 ∨ a' = 1 ∨ a' = 2 ∨ a' = 3 := by omega
    have hb'' : b' = 0 ∨ b' = 1 ∨ b' = 2 ∨ b' = 3 := by omega
    rcases ha'' with (rfl | rfl | rfl | rfl) <;>
      rcases hb'' with (rfl | rfl | rfl | rfl) <;>
        simp [I_pow_0, I_pow_1, I_pow_2, I_pow_3, I_pow_4] <;>
          norm_num <;> ring
  have h2 : (m + n : Fin 4).val = (a + b) % 4 := by rfl
  rw [h2]
  exact h_main a b ha hb

/-- 振幅的幺正性：|i^n|² = 1（对 n : Fin 4）-/
private theorem fin4_I_norm_one (n : Fin 4) :
    Complex.normSq (Complex.I ^ (n.val)) = 1 := by
  let k := n.val
  have hk : k < 4 := Fin.is_lt n
  have h_main : ∀ (k : ℕ), k < 4 → Complex.normSq (Complex.I ^ k) = 1 := by
    intro k' hk'
    have h : k' = 0 ∨ k' = 1 ∨ k' = 2 ∨ k' = 3 := by omega
    rcases h with (rfl | rfl | rfl | rfl) <;>
      simp [I_pow_0, I_pow_1, I_pow_2, I_pow_3, Complex.normSq] <;> norm_num
  exact h_main k hk

/-! 实数不等式引理（用于 fin4_I_inj）-/
private lemma real_two_ne_zero : (2 : ℝ) ≠ (0 : ℝ) := by
  have h_pos : (0 : ℝ) < (2 : ℝ) := by norm_num
  intro h_eq
  have h0 : (0 : ℝ) = (2 : ℝ) := h_eq.symm
  have h' : (2 : ℝ) < (2 : ℝ) := by
    rw [h0] at h_pos
    exact h_pos
  exact lt_irrefl (2 : ℝ) h'

private lemma real_one_ne_zero : (1 : ℝ) ≠ (0 : ℝ) := by
  have h_pos : (0 : ℝ) < (1 : ℝ) := by norm_num
  intro h_eq
  have h0 : (0 : ℝ) = (1 : ℝ) := h_eq.symm
  have h' : (1 : ℝ) < (1 : ℝ) := by
    rw [h0] at h_pos
    exact h_pos
  exact lt_irrefl (1 : ℝ) h'

private lemma real1_ne0 : (1 : ℝ) ≠ (0 : ℝ) := real_one_ne_zero
private lemma real0_ne1 : (0 : ℝ) ≠ (1 : ℝ) := by
  intro h_eq; exact real_one_ne_zero h_eq.symm

private lemma real1_ne_neg1 : (1 : ℝ) ≠ (-1 : ℝ) := by
  intro h_eq
  have h1 : (1 : ℝ) + (1 : ℝ) = (-1 : ℝ) + (1 : ℝ) := by
    exact congr_arg (fun x : ℝ => x + (1 : ℝ)) h_eq
  have h2 : (1 : ℝ) + (1 : ℝ) = (2 : ℝ) := by norm_num
  have h3 : (-1 : ℝ) + (1 : ℝ) = (0 : ℝ) := by norm_num
  have h4 : (2 : ℝ) = (0 : ℝ) := by
    rw [←h2, h1, h3]
  exact real_two_ne_zero h4

private lemma real_neg1_ne1 : (-1 : ℝ) ≠ (1 : ℝ) := by
  intro h_eq
  have h1 : (-1 : ℝ) + (1 : ℝ) = (1 : ℝ) + (1 : ℝ) := by
    exact congr_arg (fun x : ℝ => x + (1 : ℝ)) h_eq
  have h2 : (-1 : ℝ) + (1 : ℝ) = (0 : ℝ) := by norm_num
  have h3 : (1 : ℝ) + (1 : ℝ) = (2 : ℝ) := by norm_num
  have h4 : (0 : ℝ) = (2 : ℝ) := by
    rw [←h2, h1, h3]
  exact real_two_ne_zero h4.symm

private lemma real_neg1_ne0 : (-1 : ℝ) ≠ (0 : ℝ) := by
  intro h_eq
  have h1 : (-1 : ℝ) + (1 : ℝ) = (0 : ℝ) + (1 : ℝ) := by
    exact congr_arg (fun x : ℝ => x + (1 : ℝ)) h_eq
  have h2 : (-1 : ℝ) + (1 : ℝ) = (0 : ℝ) := by norm_num
  have h3 : (0 : ℝ) + (1 : ℝ) = (1 : ℝ) := by norm_num
  have h4 : (0 : ℝ) = (1 : ℝ) := by
    rw [←h2, h1, h3]
  exact real_one_ne_zero h4.symm

private lemma real0_ne_neg1 : (0 : ℝ) ≠ (-1 : ℝ) := by
  intro h_eq; exact real_neg1_ne0 h_eq.symm

private lemma c1_ne_i : (1 : ℂ) ≠ Complex.I := by
  intro h
  have hre : (1 : ℝ) = (0 : ℝ) := by
    have h2 : (Complex.I : ℂ).re = (0 : ℝ) := by
      simp [Complex.ext_iff]
      <;> norm_num
    have h3 : ((1 : ℂ).re) = (1 : ℝ) := by
      simp [Complex.ext_iff]
      <;> norm_num
    have h4 : ((1 : ℂ).re) = (Complex.I : ℂ).re := by
      rw [h]
    rw [h3, h2] at h4 <;> exact h4
  exact real_one_ne_zero hre

private lemma real_ne_one_negone : (1 : ℝ) ≠ (-1 : ℝ) := by
  intro h
  have h_pos : (0 : ℝ) < (1 : ℝ) := by norm_num
  have h_neg : (1 : ℝ) < 0 := by
    have h5 : (1 : ℝ) = (-1 : ℝ) := h
    rw [h5]; norm_num
  have h_contra : (0 : ℝ) < (0 : ℝ) := lt_trans h_pos h_neg
  exact lt_irrefl 0 h_contra

private lemma real_ne_zero_negone : (0 : ℝ) ≠ (-1 : ℝ) := by
  intro h
  have h_pos : (0 : ℝ) < (1 : ℝ) := by norm_num
  have h5 : (0 : ℝ) = (-1 : ℝ) := h
  have h6 : (1 : ℝ) = (-1 : ℝ) := by
    have h7 : (1 : ℝ) = (0 : ℝ) + (1 : ℝ) := by ring
    rw [h7, h5]; ring
  exact real_ne_one_negone h6

private lemma c1_ne_neg1 : (1 : ℂ) ≠ (-(1 : ℂ)) := by
  intro h
  let neg1c : ℂ := -(1 : ℂ)
  have hre : (1 : ℝ) = (-1 : ℝ) := by
    have h2 : ((1 : ℂ).re) = (neg1c.re) := congr_arg (fun z : ℂ => z.re) h
    have h3 : ((1 : ℂ).re) = (1 : ℝ) := by simp
    have h4 : (neg1c.re) = (-1 : ℝ) := by simp [neg1c]
    rw [h3, h4] at h2; exact h2
  exact real_ne_one_negone hre

private lemma c1_ne_negi : (1 : ℂ) ≠ (-Complex.I) := by
  intro h
  let negI : ℂ := -Complex.I
  have him : (0 : ℝ) = (-1 : ℝ) := by
    have h2 : ((1 : ℂ).im) = (negI.im) := congr_arg (fun z : ℂ => z.im) h
    have h3 : ((1 : ℂ).im) = (0 : ℝ) := by simp
    have h4 : (negI.im) = (-1 : ℝ) := by simp [negI]
    rw [h3, h4] at h2; exact h2
  exact real_ne_zero_negone him

private lemma i_ne_neg1 : Complex.I ≠ (-(1 : ℂ)) := by
  intro h
  let neg1c : ℂ := -(1 : ℂ)
  have hre : (0 : ℝ) = (-1 : ℝ) := by
    have h2 : (Complex.I.re) = (neg1c.re) := congr_arg (fun z : ℂ => z.re) h
    have h3 : (Complex.I.re) = (0 : ℝ) := by simp
    have h4 : (neg1c.re) = (-1 : ℝ) := by simp [neg1c]
    rw [h3, h4] at h2; exact h2
  exact real_ne_zero_negone hre

private lemma i_ne_negi : Complex.I ≠ (-Complex.I) := by
  intro h
  let negI : ℂ := -Complex.I
  have him : (1 : ℝ) = (-1 : ℝ) := by
    have h2 : (Complex.I.im) = (negI.im) := congr_arg (fun z : ℂ => z.im) h
    have h3 : (Complex.I.im) = (1 : ℝ) := by simp
    have h4 : (negI.im) = (-1 : ℝ) := by simp [negI]
    rw [h3, h4] at h2; exact h2
  exact real_ne_one_negone him

private lemma neg1_ne_negi : (-(1 : ℂ)) ≠ (-Complex.I) := by
  intro h
  let neg1c : ℂ := -(1 : ℂ)
  let negI : ℂ := -Complex.I
  have him : (0 : ℝ) = (-1 : ℝ) := by
    have h2 : (neg1c.im) = (negI.im) := congr_arg (fun z : ℂ => z.im) h
    have h3 : (neg1c.im) = (0 : ℝ) := by simp [neg1c]
    have h4 : (negI.im) = (-1 : ℝ) := by simp [negI]
    rw [h3, h4] at h2; exact h2
  exact real_ne_zero_negone him

/-- 振幅的单射性：若 i^(x.val) = i^(y.val)，则 x = y（对 x, y : Fin 4）-/
private theorem fin4_I_inj (x y : Fin 4) :
    (Complex.I ^ (x.val)) = (Complex.I ^ (y.val)) → x = y := by
  intro h
  apply Fin.ext
  have h_n : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 ∨ x.val = 3 := by
    have h₁ : x.val < 4 := Fin.is_lt x
    omega
  have h_m : y.val = 0 ∨ y.val = 1 ∨ y.val = 2 ∨ y.val = 3 := by
    have h₁ : y.val < 4 := Fin.is_lt y
    omega
  exact h_nm x.val y.val h h_n h_m

/-- Fin 4 加法的结合律（作为独立引理证明）-/
private theorem fin4_compose_assoc (α β γ : Fin 4) :
    (α + β) + γ = α + (β + γ) := by
  apply Fin.ext
  simp [Fin.val_add, Nat.add_assoc, Nat.mod_add_mod]

/-! ============================================================================
   §2 非平凡有限模型的显式构造
   ============================================================================ -/

/-- **非平凡有限模型**：Theory (Fin 5) (Fin 4) 的实例。

关键构造：
- input n := []                      （由 AxiomA 可满足）
- output n := (0 : Fin 5)            （常数输出，满足 compose_output）
- compose m n := m + n               （Fin 4 加法群，满足结合律）
- amplitude n := Complex.I ^ (n.val) （4 次单位根，满足 norm_one, comp_rule, injective）
- le x y := x ≤ y                    （Fin 5 标准全序）
- lt x y := x < y                    （Fin 5 标准严格全序）
- scale _ := 1                       （常函数，满足 AxiomF）
- entropy _ := 0                     （常函数，满足 AxiomI）
- gauge_group := Fin 4               （有限群，满足 AxiomH）
- spin_network := Unit               （平凡，满足 AxiomG）

本模型虽然 input 恒为空，但 M、C、振幅、因果序都非平凡，
证明 CSQIT 公理体系在受限条件下仍能容纳丰富结构。
-/
def nonTrivialFinModel : Theory (Fin 5) (Fin 4) :=
  let ft_input : Fin 4 → List (Fin 5) := fun (_ : Fin 4) => []
  let ft_output : Fin 4 → Fin 5 := fun (_ : Fin 4) => (0 : Fin 5)
  let ft_compose : Fin 4 → Fin 4 → Fin 4 := fun m n => m + n
  let ft_le : Fin 5 → Fin 5 → Prop := fun x y => x ≤ y
  let ft_lt : Fin 5 → Fin 5 → Prop := fun x y => x < y
  let ft_amplitude : Fin 4 → ℂ := fun n => Complex.I ^ (n.val)
  let ft_scale : ℕ → ℝ := fun (_ : ℕ) => (1 : ℝ)
  let ft_entropy : Set (Fin 5) → ℝ := fun (_ : Set (Fin 5)) => (0 : ℝ)

  let instA : AxiomA (Fin 5) (Fin 4) :=
    { input := ft_input,
      output := ft_output,
      input_nodup := by
        intro α
        simp [ft_input, List.Nodup],
      compose := ft_compose,
      compose_input := by
        intro α β
        simp [ft_input],
      compose_output := by
        intro α β
        simp [ft_output],
      compose_assoc := by
        intro α β γ
        simp only [ft_compose]
        exact fin4_compose_assoc α β γ }

  let instB : AxiomB (Fin 5) (Fin 4) :=
    { le := ft_le,
      lt := ft_lt,
      le_refl := by
        intro x
        simp [ft_le],
      le_trans := by
        intro x y z hxy hyz
        simp only [ft_le] at *
        <;> omega,
      le_antisymm := by
        intro x y hxy hyx
        simp only [ft_le] at *
        <;> apply Fin.ext
        <;> omega,
      lt_iff_le_not_le := by
        intro x y
        simp only [ft_le, ft_lt]
        <;> omega,
      localFinite_past := by
        intro x
        haveI : Fintype (Fin 5) := inferInstance
        exact Set.toFinite { y : Fin 5 | ft_lt y x },
      localFinite_future := by
        intro x
        haveI : Fintype (Fin 5) := inferInstance
        exact Set.toFinite { y : Fin 5 | ft_lt x y },
      weaving_axiom := by
        intro α x hx
        have hdef : ft_input α = [] := by
          simp [ft_input]
        have hdef' : (instA.input α : List (Fin 5)) = [] := by
          simpa [instA] using hdef
        rw [hdef'] at hx
        simp at hx }

  let instD : AxiomD (Fin 5) (Fin 4) :=
    { op_weaving := by
        intro α β hlt
        -- nonTrivialFinModel 中所有 output 都等于 (0 : Fin 5)，
        -- 所以 lt (output α) (output β) 恒为 False
        unfold AxiomA.output at hlt
        simp only [instA] at hlt
        -- 现在 hlt : 0 < 0，这是 Prop 而非 False
        -- 使用 Fin 5 的自反性证明矛盾
        have h : ft_output α = ft_output β := rfl
        rw [h] at hlt
        -- 现在 hlt : ft_output β < ft_output β
        contradiction }

  let instC : AxiomC (Fin 5) (Fin 4) :=
    { amplitude := ft_amplitude,
      norm_one := by
        intro α
        dsimp only [ft_amplitude]
        exact fin4_I_norm_one α,
      comp_rule := by
        intro α β
        dsimp only [ft_amplitude, instA, ft_compose]
        exact fin4_I_pow_add α β,
      amplitude_injective := by
        intro x y h
        dsimp only [ft_amplitude] at h
        exact fin4_I_inj x y h }

  let instF : AxiomF (Fin 5) (Fin 4) :=
    { scale := ft_scale,
      scale_pos := by
        intro n
        simp [ft_scale]
        <;> norm_num,
      scale_limit := fun ε hε => ⟨0, fun _ _ => by simp [ft_scale] <;> exact hε⟩ }

  let instG : AxiomG (Fin 5) (Fin 4) :=
    { spin_network := Unit,
      amplitude_spin := fun (_ : Unit) => (1 : ℂ) }

  let instH : AxiomH (Fin 5) (Fin 4) :=
    { gauge_group := Fin 4,
      field_content := fun (_ : Fin 4) (_ : Fin 5) => (0 : ℂ),
      lagrangian := fun (_ : Fin 5 → ℂ) => (0 : ℝ) }

  let instI : @AxiomI (Fin 5) (Fin 4) instA instB :=
    { entropy := ft_entropy,
      entropy_nonneg := by
        intro S
        simp [ft_entropy],
      entropy_subadditive := by
        intro S T
        simp [ft_entropy],
      information_causal := by
        intro x y _
        simp [ft_entropy] }

-- FinModel 的 AxiomJ 实例: 离散动力学编织
-- 使用 le (非严格偏序) 允许恒等映射
  let instJ : AxiomJ (Fin 5) (Fin 4) :=
    { evolve := fun (_ : Fin 4) (x : Fin 5) => x,
      causal_update := by
        intro α x
        -- 使用 instB.le_refl 来证明 ft_le x x
        exact instB.le_refl x,
      comp_evolve := by
        intro α β x
        rfl }

  { toAxiomA := instA,
    toAxiomB := instB,
    toAxiomD := instD,
    toAxiomC := instC,
    toAxiomF := instF,
    toAxiomG := instG,
    toAxiomH := instH,
    toAxiomI := instI,
    toAxiomJ := instJ }

/-! ============================================================================
   §3 模型存在性定理
   ============================================================================ -/

/-- **模型存在性**: CSQIT 理论在 M = Fin 5, C = Fin 4 下非空。
这是本模块的主定理。-/
theorem csqit_has_nonTrivial_model : Nonempty (Theory (Fin 5) (Fin 4)) :=
  ⟨nonTrivialFinModel⟩

instance : Inhabited (Theory (Fin 5) (Fin 4)) := ⟨nonTrivialFinModel⟩

end CSQIT.Models.FinModel5x4
