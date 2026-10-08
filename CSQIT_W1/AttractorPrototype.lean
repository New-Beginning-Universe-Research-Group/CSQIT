import Mathlib.Data.Nat.GCD.Basic
import CSQIT_W1.MinimalCost

namespace CSQIT_W1.AttractorPrototype

set_option linter.unusedVariables false

def alpha_integer_part (p1 p2 p4 : ℕ) : ℕ := p1^p4 + p1^p2 + 1
def alpha_fraction_eq (p1 p2 p3 : ℕ) : Prop := p2^p1 * 250 = 9 * p1 * p3^p2

/-! 引理 1: p₁ 必须是 2 -/
lemma lock_p1_eq_2 :
    ∀ p₁ p₂ p₃ p₄ : ℕ,
    p₁ ≥ 2 → p₂ > p₁ → p₃ > p₂ → p₄ > p₃ →
    alpha_integer_part p₁ p₂ p₄ = 137 →
    p₁ = 2 := by
  intro p₁ p₂ p₃ p₄ h1 h2 h3 h4 hint
  by_contra h
  have hge3 : p₁ ≥ 3 := by omega
  have h_steps : p₄ ≥ p₁ + 3 := by omega
  have hp4ge6 : p₄ ≥ 6 := by omega
  have h_sum : p₁^p₄ + p₁^p₂ = 136 := by
    have h' : p₁^p₄ + p₁^p₂ + 1 = 137 := by simpa [alpha_integer_part] using hint
    omega
  have hpos_p2 : 0 < p₁^p₂ := by positivity
  have hp4lt : p₁^p₄ ≤ 136 := by linarith
  have hp4bnd : p₄ ≤ 6 := by
    by_contra hc
    have hc' : p₄ ≥ 7 := by linarith
    have h1 : 3^p₄ ≤ p₁^p₄ := by apply pow_le_pow <;> linarith
    have h2 : 3^7 ≤ 3^p₄ := by apply pow_le_pow <;> norm_num <;> linarith
    have h3 : 3^7 ≤ p₁^p₄ := by linarith
    have h2187 : 3^7 = 2187 := by norm_num
    have hlt : p₁^p₄ ≤ 136 := hp4lt
    rw [h2187] at h3
    linarith
  have hp4eq6 : p₄ = 6 := by omega
  have hp2eq4 : p₂ = 4 := by omega
  have hp3eq5 : p₃ = 5 := by omega
  have hp1eq3 : p₁ = 3 := by omega
  rw [hp4eq6, hp2eq4, hp1eq3] at h_sum
  norm_num at h_sum

/-! 引理 2: p₂ > 2, p₄ > p₂, 2^p₂ + 2^p₄ = 136 → p₂ = 3 -/
lemma lock_p2_eq_3 :
    ∀ p₂ p₄ : ℕ,
    p₂ > 2 → p₄ > p₂ →
    2^p₂ + 2^p₄ = 136 →
    p₂ = 3 := by
  intro p₂ p₄ hgt hgt2 h_eq
  have hp2ge3 : p₂ ≥ 3 := by linarith
  have hp4bnd : p₄ ≤ 7 := by
    by_contra hc
    have hc' : p₄ ≥ 8 := by linarith
    have h1 : 2^8 ≤ 2^p₄ := by apply pow_le_pow <;> norm_num <;> linarith
    have h256 : 2^8 = 256 := by norm_num
    have hpos : 0 ≤ 2^p₂ := by positivity
    have hp4lt : 2^p₄ ≤ 136 := by linarith
    rw [h256] at h1
    linarith
  have hp2bnd : p₂ ≤ 6 := by
    by_contra hc
    have hc' : p₂ ≥ 7 := by linarith
    have h1 : 2^7 ≤ 2^p₂ := by apply pow_le_pow <;> norm_num <;> linarith
    have h128 : 2^7 = 128 := by norm_num
    have hpos : 0 ≤ 2^p₄ := by positivity
    have hp2lt : 2^p₂ ≤ 136 := by linarith
    rw [h128] at h1
    linarith
  have hcases : p₂ = 3 ∨ p₂ = 4 ∨ p₂ = 5 ∨ p₂ = 6 := by omega
  rcases hcases with (rfl | h4 | h5 | h6)
  · rfl
  · subst h4
    have hcases2 : p₄ = 5 ∨ p₄ = 6 ∨ p₄ = 7 := by omega
    rcases hcases2 with (rfl | rfl | rfl) <;> norm_num at h_eq
  · subst h5
    have hcases2 : p₄ = 6 ∨ p₄ = 7 := by omega
    rcases hcases2 with (rfl | rfl) <;> norm_num at h_eq
  · subst h6
    have hcases2 : p₄ = 7 := by omega
    rcases hcases2 with rfl
    norm_num at h_eq

/-! 引理 3: 2^p₄ = 128, p₄ > 3 → p₄ = 7 -/
lemma lock_p4_eq_7 :
    ∀ p₄ : ℕ,
    p₄ > 3 → 2^p₄ = 128 → p₄ = 7 := by
  intro p₄ hgt h
  have hp4ge4 : p₄ ≥ 4 := by linarith
  have hp4bnd : p₄ ≤ 7 := by
    by_contra hc
    have hc' : p₄ ≥ 8 := by linarith
    have h1 : 2^8 ≤ 2^p₄ := by apply pow_le_pow <;> norm_num <;> linarith
    have h256 : 2^8 = 256 := by norm_num
    rw [h256] at h1
    linarith
  have hcases : p₄ = 4 ∨ p₄ = 5 ∨ p₄ = 6 ∨ p₄ = 7 := by omega
  rcases hcases with (h4 | h5 | h6 | h7)
  · subst h4; norm_num at h
  · subst h5; norm_num at h
  · subst h6; norm_num at h
  · exact h7

/-! 引理 4: 分数等式 → p₃ = 5 -/
lemma lock_p3_eq_5 :
    ∀ p₃ : ℕ, alpha_fraction_eq 2 3 p₃ → p₃ = 5 := by
  intro p₃ hfrac
  have h : 3^2 * 250 = 9 * 2 * p₃^3 := hfrac
  have h' : 2250 = 18 * p₃^3 := by norm_num at h ⊢ <;> exact h
  have h'' : p₃^3 = 125 := by linarith
  have hbnd2 : p₃ ≥ 2 := by
    by_contra hc
    have hc01 : p₃ = 0 ∨ p₃ = 1 := by omega
    rcases hc01 with (rfl | rfl) <;> norm_num at h''
  have hbnd5 : p₃ ≤ 5 := by
    by_contra hc
    have hc' : p₃ ≥ 6 := by linarith
    have h1 : 6^3 ≤ p₃^3 := by apply pow_le_pow <;> linarith <;> norm_num
    have h2 : 6^3 = 216 := by norm_num
    have h216 : p₃^3 ≥ 216 := by linarith
    have hz125 : (125 : ℤ) < 216 := by norm_num
    have hz216 : (↑(p₃^3) : ℤ) ≥ 216 := by exact_mod_cast h216
    have hz_eq : (↑(p₃^3) : ℤ) = 125 := by exact_mod_cast h''
    linarith
  have hcases : p₃ = 2 ∨ p₃ = 3 ∨ p₃ = 4 ∨ p₃ = 5 := by omega
  rcases hcases with (h2 | h3 | h4 | h5)
  · subst h2; norm_num at h''
  · subst h3; norm_num at h''
  · subst h4; norm_num at h''
  · exact h5

/-! 主定理：吸引子唯一性。 -/
theorem attractor_unique :
    ∀ p₁ p₂ p₃ p₄ : ℕ,
    p₁ ≥ 2 → p₂ > p₁ → p₃ > p₂ → p₄ > p₃ →
    alpha_integer_part p₁ p₂ p₄ = 137 →
    alpha_fraction_eq p₁ p₂ p₃ →
    p₁ = 2 ∧ p₂ = 3 ∧ p₃ = 5 ∧ p₄ = 7 := by
  intro p₁ p₂ p₃ p₄ h1 h2 h3 h4 hint hfrac
  have h_p1 : p₁ = 2 := lock_p1_eq_2 p₁ p₂ p₃ p₄ h1 h2 h3 h4 hint
  subst h_p1
  have h_sum136 : 2^p₂ + 2^p₄ = 136 := by
    have h' : alpha_integer_part 2 p₂ p₄ = 137 := hint
    dsimp [alpha_integer_part] at h' ⊢
    linarith
  have h_p2 : p₂ = 3 := lock_p2_eq_3 p₂ p₄ (by linarith) (by linarith) h_sum136
  have h_p4_eq_pow : 2^p₄ = 128 := by
    have h : 2^3 + 2^p₄ = 136 := by rw [h_p2] at h_sum136; exact h_sum136
    norm_num at h ⊢ <;> linarith
  have h_p4 : p₄ = 7 := lock_p4_eq_7 p₄ (by linarith) h_p4_eq_pow
  have h_p3 : p₃ = 5 := by
    have h' : alpha_fraction_eq 2 p₂ p₃ := hfrac
    rw [h_p2] at h'
    exact lock_p3_eq_5 p₃ h'
  exact ⟨by rfl, h_p2, h_p3, h_p4⟩

end CSQIT_W1.AttractorPrototype
