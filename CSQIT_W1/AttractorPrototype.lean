import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.IntervalCases
import CSQIT_W1.MinimalCost

namespace CSQIT_W1.AttractorPrototype

set_option linter.unusedVariables false

/-!
## 吸引子唯一性定理 — 原型 v3（修复版）

路径 A（代数分治）核心：
  整数部分大小约束 → 锁 p₁=2 → 锁 p₂=3 → 锁 p₄=7
  分数等式 p₃³=125 → 锁 p₃=5
  每步只处理 1 个变量，纯不等式 + norm_num。
  不假设素数——仅假设递增自然数 p₁ ≥ 2！
-/

def alpha_integer_part (p1 p2 p4 : ℕ) : ℕ := p1^p4 + p1^p2 + 1
def alpha_fraction_eq (p1 p2 p3 : ℕ) : Prop := p2^p1 * 250 = 9 * p1 * p3^p2

/-! 引理 1: p₁ 必须是 2（大小约束） -/
lemma lock_p1_eq_2 :
    ∀ p₁ p₂ p₃ p₄ : ℕ,
    p₁ ≥ 2 → p₂ > p₁ → p₃ > p₂ → p₄ > p₃ →
    alpha_integer_part p₁ p₂ p₄ = 137 →
    p₁ = 2 := by
  intro p₁ p₂ p₃ p₄ h1 h2 h3 h4 hint
  have hp4_ge_p13 : p₄ ≥ p₁ + 3 := by omega
  by_cases hcontra : p₁ ≥ 3
  · have hp4ge6 : p₄ ≥ 6 := by omega
    have hpowbig : p₁^p₄ ≥ 729 := by
      calc p₁^p₄ ≥ 3^p₄ := by gcongr
           _ ≥ 3^6 := by gcongr
           _ = 729 := by norm_num
    have hsum : p₁^p₄ + p₁^p₂ + 1 ≥ 729 := by
      have hge : p₁^p₂ ≥ p₁ := by
        have h2 : p₂ ≥ p₁ + 1 := by omega
        gcongr
      omega
    dsimp [alpha_integer_part] at hint
    omega
  · have hlt3 : p₁ < 3 := by omega
    omega

/-! 引理 2a: 由 p₄ ≥ p₂ + 2 推出 2^{p₂} ≤ 27 -/
lemma p2_pow_le_27 :
    ∀ p₂ p₄ : ℕ,
    p₂ > 2 → p₄ ≥ p₂ + 2 →
    2^p₂ + 2^p₄ = 136 →
    2^p₂ ≤ 27 := by
  intro p₂ p₄ hp2 hge h_eq
  have h5 : 2^p₄ ≥ 2^(p₂ + 2) := by gcongr
  have h6 : 2^(p₂ + 2) = 4 * 2^p₂ := by
    calc 2^(p₂ + 2) = 2^p₂ * 2^2 := by ring_nf
         _ = 4 * 2^p₂ := by ring
  have h7 : 2^p₄ ≥ 4 * 2^p₂ := by linarith
  omega

/-! 引理 2b: 2^{p₂} ≤ 27 且 p₂ > 2 → p₂ ≤ 4 -/
lemma p2_le_4 :
    ∀ p₂ : ℕ, p₂ > 2 → 2^p₂ ≤ 27 → p₂ ≤ 4 := by
  intro p₂ hgt hle
  by_contra hc
  have h5 : p₂ ≥ 5 := by omega
  have h6 : 2^p₂ ≥ 2^5 := by gcongr
  have h7 : 2^p₂ ≥ 32 := by norm_num at h6 ⊢ <;> linarith
  linarith

/-! 引理 2c: 关键 — 若 p₄ = p₂ + 1 则 3 ∣ 136 (矛盾) -/
lemma p4_eq_p2_plus_1_impossible :
    ∀ p₂ p₄ : ℕ,
    p₂ > 2 → p₄ = p₂ + 1 →
    2^p₂ + 2^p₄ = 136 → False := by
  intro p₂ p₄ hgt heq h_eq
  have h5 : 2^p₂ + 2^(p₂ + 1) = 136 := by rw [heq] at h_eq; exact h_eq
  have h6 : 3 * 2^p₂ = 136 := by
    have h7 : 2^(p₂ + 1) = 2 * 2^p₂ := by ring
    linarith
  have h9 : (3 : ℕ) ∣ 136 := by omega
  norm_num at h9

/-! 引理 2d: p₂ > 2, p₄ > p₂, 2^p₂ + 2^p₄ = 136 → p₂ = 3 -/
lemma lock_p2_eq_3 :
    ∀ p₂ p₄ : ℕ,
    p₂ > 2 → p₄ > p₂ →
    2^p₂ + 2^p₄ = 136 →
    p₂ = 3 := by
  intro p₂ p₄ hgt hgt2 h_eq
  have hp4ge_p21 : p₄ ≥ p₂ + 1 := by omega
  have hp2le4 : p₂ ≤ 4 := by
    by_cases hcases : p₄ ≥ p₂ + 2 ∨ p₄ = p₂ + 1
    · rcases hcases with hge | heq
      · have hp2le27 : 2^p₂ ≤ 27 := p2_pow_le_27 p₂ p₄ hgt hge h_eq
        exact p2_le_4 p₂ hgt hp2le27
      · exact False.elim (p4_eq_p2_plus_1_impossible p₂ p₄ hgt heq h_eq)
    · omega
  by_cases h2 : p₂ = 3
  · exact h2
  · have h4 : p₂ = 4 := by omega
    rw [h4] at h_eq
    have hp4ge5 : p₄ ≥ 5 := by omega
    have hcases : p₄ = 5 ∨ p₄ = 6 ∨ p₄ ≥ 7 := by omega
    rcases hcases with h5 | h6 | hge7
    · rw [h5] at h_eq; norm_num at h_eq
    · rw [h6] at h_eq; norm_num at h_eq
    · have hge128 : (2^p₄ : ℕ) ≥ 128 := by
        have h : (2^p₄ : ℕ) ≥ 2^7 := by gcongr
        have h7 : (2^7 : ℕ) = 128 := by norm_num
        linarith
      have h_eq2 : (2^p₄ : ℕ) = 136 - 2^4 := by omega
      have h_eq3 : (2^p₄ : ℕ) = 120 := by norm_num at h_eq2 ⊢
      have h128gt120 : (128 : ℤ) > 120 := by norm_num
      have hge128z : (↑(2^p₄) : ℤ) ≥ 128 := by exact_mod_cast hge128
      have h120z : (↑(2^p₄) : ℤ) = 120 := by exact_mod_cast h_eq3
      linarith

/-! 引理 3: 2^p₄ = 128, p₄ > 3 → p₄ = 7 -/
lemma lock_p4_eq_7 :
    ∀ p₄ : ℕ,
    p₄ > 3 → 2^p₄ = 128 → p₄ = 7 := by
  intro p₄ hgt h
  have hcases : p₄ = 4 ∨ p₄ = 5 ∨ p₄ = 6 ∨ p₄ = 7 ∨ p₄ ≥ 8 := by omega
  rcases hcases with h4 | h5 | h6 | h7 | hge8
  · rw [h4] at h; norm_num at h
  · rw [h5] at h; norm_num at h
  · rw [h6] at h; norm_num at h
  · rw [h7]
  · have hge256 : (2^p₄ : ℕ) ≥ 256 := by
      have h : (2^p₄ : ℕ) ≥ 2^8 := by gcongr
      have h8 : (2^8 : ℕ) = 256 := by norm_num
      linarith
    have h256pos : (256 : ℤ) > 128 := by norm_num
    have hge256z : (↑(2^p₄) : ℤ) ≥ 256 := by exact_mod_cast hge256
    have h128z : (↑(2^p₄) : ℤ) = 128 := by exact_mod_cast h
    linarith

/-! 引理 4: 分数等式 → p₃ = 5 -/
lemma lock_p3_eq_5 :
    ∀ p₃ : ℕ, alpha_fraction_eq 2 3 p₃ → p₃ = 5 := by
  intro p₃ hfrac
  have h : 3^2 * 250 = 9 * 2 * p₃^3 := hfrac
  have h' : 2250 = 18 * p₃^3 := by norm_num at h ⊢ <;> exact h
  have h'' : p₃^3 = 125 := by omega
  have hge5 : p₃ ≥ 5 := by
    by_contra hc
    have hc' : p₃ ≤ 4 := by omega
    have h9 : p₃^3 ≤ 4^3 := by gcongr
    have h10 : p₃^3 ≤ 64 := by norm_num at h9 ⊢ <;> linarith
    linarith
  have hle5 : p₃ ≤ 5 := by
    by_contra hc
    have hc' : p₃ ≥ 6 := by omega
    have h9 : p₃^3 ≥ 6^3 := by gcongr
    have h10 : p₃^3 ≥ 216 := by norm_num at h9 ⊢ <;> linarith
    linarith
  omega

/-! 主定理：吸引子唯一性。不假设素数！ -/
theorem attractor_unique :
    ∀ p₁ p₂ p₃ p₄ : ℕ,
    p₁ ≥ 2 → p₂ > p₁ → p₃ > p₂ → p₄ > p₃ →
    alpha_integer_part p₁ p₂ p₄ = 137 →
    alpha_fraction_eq p₁ p₂ p₃ →
    p₁ = 2 ∧ p₂ = 3 ∧ p₃ = 5 ∧ p₄ = 7 := by
  intro p₁ p₂ p₃ p₄ h1 h2 h3 h4 hint hfrac
  have h_p1 : p₁ = 2 := lock_p1_eq_2 p₁ p₂ p₃ p₄ h1 h2 h3 h4 hint
  subst h_p1
  have h_int' : 2^p₂ + 2^p₄ + 1 = 137 := by
    have h' : alpha_integer_part 2 p₂ p₄ = 137 := hint
    dsimp [alpha_integer_part] at h' ⊢
    linarith
  have h_sum136 : 2^p₂ + 2^p₄ = 136 := by linarith
  have h_p2 : p₂ = 3 := lock_p2_eq_3 p₂ p₄ (by omega) (by omega) h_sum136
  have h_p4_eq_pow : 2^p₄ = 128 := by
    have h : 2^3 + 2^p₄ = 136 := by rw [h_p2] at h_sum136; exact h_sum136
    norm_num at h ⊢ <;> linarith
  have h_p4 : p₄ = 7 := lock_p4_eq_7 p₄ (by omega) h_p4_eq_pow
  have h_p3 : p₃ = 5 := by
    have h' : alpha_fraction_eq 2 p₂ p₃ := hfrac
    rw [h_p2] at h'
    exact lock_p3_eq_5 p₃ h'
  exact ⟨by rfl, h_p2, h_p3, h_p4⟩

end CSQIT_W1.AttractorPrototype
