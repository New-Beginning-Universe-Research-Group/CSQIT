/-
================================================================================
CSQIT_V1Bridge — 非全序因果模型（G17）
模块: CSQIT_V1Bridge.NonTotalModel
版本: v0.1.0（2026-11-07）
================================================================================

`CausalSetWitness` 证明见证模型给出一个**链**（线性时间）。本模块给出
一个同样合法、振幅非平凡、但典范因果序**非全序**的 v23 模型，
从而否定「v23 组合结构强制线性全局时间」：

  C = (ℕ × ℕ) \ {(0,0)},  compose u v = u + v（分量加法）,
  amplitude(u) = exp(i·2π·(√2·u₁ + √3·u₂)).

  · G17a（A）：AxiomA + AxiomC 成立（振幅单射归约为 √2、√3、√6 无理）；
  · G17b（A）：典范可达序恰为分量偏序（u ≤ v 且 u ≠ v）；
  · G17c（A）：该序是严格偏序且与 compose 相容，故承载因果层；
  · G17d（A）：该序非全序——(1,0) 与 (0,1) 不可比。

因此「因果序是否为链」在 v23 中是**模型相关**的，不能由 compose +
振幅单射导出；线性时间必须作为额外结构假设（对应 V1 的全局时间/
层级选择），属 B/C 档交界，本轮只登记为「不可由现有结构强制」。

注：由 `TwoAspectNoFinite`，AxiomC 模型必 `compose` 交换；本模型
确为交换（分量加法），与既有框架一致，不构成冲突。

纪律：零新增 axiom、零 sorry；不修改既有文件。
================================================================================ -/

import CSQIT_V1Bridge.CausalSetWitness
import Mathlib.NumberTheory.Real.Irrational

namespace CSQIT_V1Bridge

open CSQIT_W1.CompilerAxioms
open CSQIT_W1.Foundation
open Complex
open Real

/-! ============================================================================
    §1. G17a：乘积模型与振幅单射
   ============================================================================ -/

/-- 载体：非零自然数对。 -/
abbrev PairRule : Type := {p : ℕ × ℕ // p ≠ (0, 0)}

/-- 组合：分量加法。 -/
def pairCompose (u v : PairRule) : PairRule :=
  ⟨(u.val.1 + v.val.1, u.val.2 + v.val.2), by
    intro hzero
    have h1 : u.val.1 + v.val.1 = 0 := congrArg Prod.fst hzero
    have h2 : u.val.2 + v.val.2 = 0 := congrArg Prod.snd hzero
    have hu1 : u.val.1 = 0 := by omega
    have hu2 : u.val.2 = 0 := by omega
    exact u.property (Prod.ext hu1 hu2)⟩

/-- 相位角：`2π(√2 u₁ + √3 u₂)`。 -/
noncomputable def pairAngle (u : PairRule) : ℝ :=
  (2 * π) * (Real.sqrt 2 * (u.val.1 : ℝ) + Real.sqrt 3 * (u.val.2 : ℝ))

/-- 振幅：`exp(i·pairAngle)`。 -/
noncomputable def pairAmplitude (u : PairRule) : ℂ :=
  (Circle.exp (pairAngle u) : ℂ)

/-- `3` 不是平方数（供 `irrational_sqrt_natCast_iff` 使用）。 -/
theorem not_isSquare_three : ¬ IsSquare 3 := by
  rintro ⟨r, hr⟩
  rcases Nat.lt_or_ge r 3 with h | h
  · interval_cases r <;> norm_num at hr
  · have hge : 9 ≤ r * r := Nat.mul_le_mul h h
    omega

/-- `6` 不是平方数。 -/
theorem not_isSquare_six : ¬ IsSquare 6 := by
  rintro ⟨r, hr⟩
  rcases Nat.lt_or_ge r 3 with h | h
  · interval_cases r <;> norm_num at hr
  · have hge : 9 ≤ r * r := Nat.mul_le_mul h h
    omega

/-- **G17a（W1，A 档）**：`ℤ` 上 `√2, √3` 的线性无关性。
    即 `√2·A + √3·B = m` 只有平凡解。

    证明分三种情形：`A = 0`、`B = 0` 直接用 `√2`/`√3` 无理；
    一般情形平方后得到 `√6` 的有理表达式，与 `√6` 无理矛盾。 -/
theorem sqrt_two_three_linear_independent (A B m : ℤ)
    (h : Real.sqrt 2 * (A : ℝ) + Real.sqrt 3 * (B : ℝ) = (m : ℝ)) :
    A = 0 ∧ B = 0 := by
  have hs2 : Irrational (Real.sqrt 2) := irrational_sqrt_two
  have hs3 : Irrational (Real.sqrt 3) :=
    irrational_sqrt_natCast_iff.mpr not_isSquare_three
  have hs6 : Irrational (Real.sqrt 6) :=
    irrational_sqrt_natCast_iff.mpr not_isSquare_six
  by_cases hA : A = 0
  · subst hA
    have h3 : Real.sqrt 3 * (B : ℝ) = (m : ℝ) := by simpa using h
    by_cases hB : B = 0
    · exact ⟨rfl, hB⟩
    · exfalso
      have hBreal : (B : ℝ) ≠ 0 := by exact_mod_cast hB
      refine hs3 ⟨(m : ℚ) / (B : ℚ), ?_⟩
      push_cast
      field_simp [hBreal]
      linarith
  · by_cases hB : B = 0
    · subst hB
      have h2 : Real.sqrt 2 * (A : ℝ) = (m : ℝ) := by simpa using h
      exfalso
      have hAreal : (A : ℝ) ≠ 0 := by exact_mod_cast hA
      refine hs2 ⟨(m : ℚ) / (A : ℚ), ?_⟩
      push_cast
      field_simp [hAreal]
      linarith
    · exfalso
      have hAreal : (A : ℝ) ≠ 0 := by exact_mod_cast hA
      have hBreal : (B : ℝ) ≠ 0 := by exact_mod_cast hB
      have hsq : (Real.sqrt 2 * (A : ℝ) + Real.sqrt 3 * (B : ℝ)) ^ 2 = (m : ℝ) ^ 2 := by
        rw [h]
      have h6 : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
        rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) 3]
        norm_num
      have hexp : (Real.sqrt 2 * (A : ℝ) + Real.sqrt 3 * (B : ℝ)) ^ 2 =
          2 * (A : ℝ) ^ 2 + 3 * (B : ℝ) ^ 2 +
            Real.sqrt 6 * (2 * (A : ℝ) * (B : ℝ)) := by
        have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        calc
          (Real.sqrt 2 * (A : ℝ) + Real.sqrt 3 * (B : ℝ)) ^ 2
              = (Real.sqrt 2) ^ 2 * (A : ℝ) ^ 2 +
                2 * (Real.sqrt 2 * (A : ℝ)) * (Real.sqrt 3 * (B : ℝ)) +
                (Real.sqrt 3) ^ 2 * (B : ℝ) ^ 2 := by ring
          _ = 2 * (A : ℝ) ^ 2 + 2 * (Real.sqrt 2 * Real.sqrt 3) *
                ((A : ℝ) * (B : ℝ)) + 3 * (B : ℝ) ^ 2 := by
                rw [h2, h3]; ring
          _ = 2 * (A : ℝ) ^ 2 + 2 * Real.sqrt 6 * ((A : ℝ) * (B : ℝ)) +
                3 * (B : ℝ) ^ 2 := by rw [h6]
          _ = 2 * (A : ℝ) ^ 2 + 3 * (B : ℝ) ^ 2 +
                Real.sqrt 6 * (2 * (A : ℝ) * (B : ℝ)) := by ring
      have hkey : Real.sqrt 6 * (2 * (A : ℝ) * (B : ℝ)) =
          (m : ℝ) ^ 2 - 2 * (A : ℝ) ^ 2 - 3 * (B : ℝ) ^ 2 := by
        rw [hexp] at hsq
        linarith
      refine hs6 ⟨((m : ℚ) ^ 2 - 2 * (A : ℚ) ^ 2 - 3 * (B : ℚ) ^ 2) /
        (2 * (A : ℚ) * (B : ℚ)), ?_⟩
      push_cast
      field_simp [hAreal, hBreal]
      linarith [hkey]

/-- **G17a（W1，A 档）**：乘积模型的 `AxiomA` 实例。 -/
instance pairAxiomA : AxiomA Unit PairRule where
  input := fun _ => []
  output := fun _ => ()
  input_nodup := by
    intro _
    simp
  compose := pairCompose
  compose_input := by
    intro _ _
    simp
  compose_output := by
    intro _ _
    simp
  compose_assoc := by
    intro a b c
    apply Subtype.ext
    apply Prod.ext <;> simp [pairCompose, Nat.add_assoc]

/-- **G17a（W1，A 档）**：乘积模型的 `AxiomC` 实例。 -/
noncomputable instance pairAxiomC : AxiomC Unit PairRule where
  amplitude := pairAmplitude
  norm_one := by
    intro u
    have hnorm : ‖(Circle.exp (pairAngle u) : ℂ)‖ = 1 := Circle.norm_coe _
    rw [pairAmplitude, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  comp_rule := by
    intro u v
    change (Circle.exp (pairAngle (pairCompose u v)) : ℂ) =
      (Circle.exp (pairAngle u) : ℂ) * (Circle.exp (pairAngle v) : ℂ)
    have harg : pairAngle (pairCompose u v) = pairAngle u + pairAngle v := by
      unfold pairAngle pairCompose
      push_cast
      ring
    rw [harg, Circle.exp_add]
    simp
  amplitude_injective := by
    intro u v h
    have hcirc : Circle.exp (pairAngle u) = Circle.exp (pairAngle v) := by
      simpa only [pairAmplitude] using Subtype.ext h
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hcirc
    have h1 : pairAngle u - pairAngle v = (m : ℝ) * (2 * π) := by
      linarith
    have hpi_ne : (2 * π : ℝ) ≠ 0 := by positivity
    have hdiv : (pairAngle u - pairAngle v) / (2 * π) = (m : ℝ) := by
      rw [h1]
      field_simp
    have harg : (pairAngle u - pairAngle v) / (2 * π) =
        Real.sqrt 2 * ((u.val.1 : ℝ) - (v.val.1 : ℝ)) +
        Real.sqrt 3 * ((u.val.2 : ℝ) - (v.val.2 : ℝ)) := by
      unfold pairAngle
      field_simp [hpi_ne]
      ring
    have hsqrt_eq : Real.sqrt 2 * ((u.val.1 : ℝ) - (v.val.1 : ℝ)) +
        Real.sqrt 3 * ((u.val.2 : ℝ) - (v.val.2 : ℝ)) = (m : ℝ) := by
      rw [harg] at hdiv
      exact hdiv
    let A : ℤ := (u.val.1 : ℤ) - (v.val.1 : ℤ)
    let B : ℤ := (u.val.2 : ℤ) - (v.val.2 : ℤ)
    have hAcast : (A : ℝ) = (u.val.1 : ℝ) - (v.val.1 : ℝ) := by
      dsimp [A]
      push_cast
      ring
    have hBcast : (B : ℝ) = (u.val.2 : ℝ) - (v.val.2 : ℝ) := by
      dsimp [B]
      push_cast
      ring
    have hind : Real.sqrt 2 * (A : ℝ) + Real.sqrt 3 * (B : ℝ) = (m : ℝ) := by
      rw [hAcast, hBcast]
      exact hsqrt_eq
    obtain ⟨hA0, hB0⟩ := sqrt_two_three_linear_independent A B m hind
    have hu1 : u.val.1 = v.val.1 := by
      have hz : (u.val.1 : ℤ) - (v.val.1 : ℤ) = 0 := by simpa [A] using hA0
      omega
    have hu2 : u.val.2 = v.val.2 := by
      have hz : (u.val.2 : ℤ) - (v.val.2 : ℤ) = 0 := by simpa [B] using hB0
      omega
    exact Subtype.ext (Prod.ext hu1 hu2)

/-! ============================================================================
    §2. G17b–d：典范因果序与非线性
   ============================================================================ -/

/-- 乘积模型上的可达关系。 -/
def pairReach (u v : PairRule) : Prop :=
  ∃ w : PairRule, v = pairCompose u w ∧ v ≠ u

/-- **G17b（W1，A 档）**：可达序恰为分量偏序（去掉对角）。 -/
theorem pairReach_iff (u v : PairRule) :
    pairReach u v ↔ u.val.1 ≤ v.val.1 ∧ u.val.2 ≤ v.val.2 ∧ u ≠ v := by
  constructor
  · rintro ⟨w, hv, hne⟩
    have h1 : v.val.1 = u.val.1 + w.val.1 := by
      have := congrArg (fun p : PairRule => p.val.1) hv
      simpa [pairCompose] using this
    have h2 : v.val.2 = u.val.2 + w.val.2 := by
      have := congrArg (fun p : PairRule => p.val.2) hv
      simpa [pairCompose] using this
    exact ⟨by omega, by omega, fun h => hne h.symm⟩
  · rintro ⟨h1, h2, hne⟩
    let w : PairRule := ⟨(v.val.1 - u.val.1, v.val.2 - u.val.2), by
      intro hzero
      have hw1 : v.val.1 - u.val.1 = 0 := congrArg Prod.fst hzero
      have hw2 : v.val.2 - u.val.2 = 0 := congrArg Prod.snd hzero
      have hu1 : u.val.1 = v.val.1 := by omega
      have hu2 : u.val.2 = v.val.2 := by omega
      exact hne (Subtype.ext (Prod.ext hu1 hu2))⟩
    refine ⟨w, ?_, fun h => hne h.symm⟩
    apply Subtype.ext
    apply Prod.ext <;> simp [pairCompose, w] <;> omega

/-- **G17c-1（W1，A 档）**：可达序无自环。 -/
theorem pairReach_irrefl (u : PairRule) : ¬ pairReach u u := by
  rw [pairReach_iff]
  intro h
  exact h.2.2 rfl

/-- **G17c-2（W1，A 档）**：可达序传递。 -/
theorem pairReach_trans {u v w : PairRule} (huv : pairReach u v) (hvw : pairReach v w) :
    pairReach u w := by
  rw [pairReach_iff] at huv hvw ⊢
  obtain ⟨h11, h12, h13⟩ := huv
  obtain ⟨h21, h22, h23⟩ := hvw
  refine ⟨by omega, by omega, ?_⟩
  intro huw
  have hw1 : w.val.1 = u.val.1 := congrArg (fun p : PairRule => p.val.1) huw.symm
  have hw2 : w.val.2 = u.val.2 := congrArg (fun p : PairRule => p.val.2) huw.symm
  have hv1 : v.val.1 = u.val.1 := by omega
  have hv2 : v.val.2 = u.val.2 := by omega
  exact h13 (Subtype.ext (Prod.ext hv1.symm hv2.symm))

/-- **G17c-3（W1，A 档）**：乘积模型无右作用元。 -/
theorem pair_no_right_id (u v : PairRule) : pairCompose u v ≠ u := by
  intro h
  have h1 : u.val.1 + v.val.1 = u.val.1 :=
    congrArg (fun p : PairRule => p.val.1) h
  have h2 : u.val.2 + v.val.2 = u.val.2 :=
    congrArg (fun p : PairRule => p.val.2) h
  have hv1 : v.val.1 = 0 := by omega
  have hv2 : v.val.2 = 0 := by omega
  exact v.property (Prod.ext hv1 hv2)

/-- **G17c-4（W1，A 档）**：可达序与 `compose` 相容。 -/
theorem pairReach_compat (u v : PairRule) : pairReach u (pairCompose u v) :=
  ⟨v, rfl, pair_no_right_id u v⟩

/-- **G17c（W1，A 档）**：乘积模型上的典范因果-振幅层（序 = 可达序）。 -/
def pairLayer : V1CausalAmplitudeLayer (M := Unit) (C := PairRule) where
  causalOrder := pairReach
  irrefl := pairReach_irrefl
  trans := fun _ _ _ => pairReach_trans
  compat := pairReach_compat
  phase_compat := phase_compat_of_causal_fields pairReach_irrefl pairReach_compat

/-- **G17d（W1，A 档）**：典范因果序非全序。
    取 `u = (1,0)`、`v = (0,1)`：两者互不可达。 -/
theorem pairReach_not_total :
    ¬ ∀ u v : PairRule, u ≠ v → pairReach u v ∨ pairReach v u := by
  intro htotal
  let u : PairRule := ⟨(1, 0), by simp⟩
  let v : PairRule := ⟨(0, 1), by simp⟩
  have huv : u ≠ v := by
    intro heq
    have h1 : u.val.1 = v.val.1 := congrArg (fun p : PairRule => p.val.1) heq
    simp [u, v] at h1
  rcases htotal u v huv with hr | hr
  · rw [pairReach_iff] at hr
    have h1 := hr.1
    simp [u, v] at h1
  · rw [pairReach_iff] at hr
    have h2 := hr.2.1
    simp [u, v] at h2

/-- **G17（W1，A 档，总结）**：存在合法的 v23 模型（AxiomA + AxiomC，
    振幅非平凡、载体无限、无右作用元），其典范因果-振幅层的因果序
    是严格偏序但**不是**全序。因此 v23 结构不强制线性全局时间。 -/
theorem exists_nontotal_causal_layer :
    ∃ (M C : Type) (_A : AxiomA M C) (_Cx : AxiomC M C)
      (layer : V1CausalAmplitudeLayer (M := M) (C := C)),
      (∀ x : C, ¬ layer.causalOrder x x) ∧
      (∀ x y z : C, layer.causalOrder x y → layer.causalOrder y z →
        layer.causalOrder x z) ∧
      ¬ (∀ x y : C, x ≠ y → layer.causalOrder x y ∨ layer.causalOrder y x) :=
  ⟨Unit, PairRule, pairAxiomA, pairAxiomC, pairLayer,
    pairReach_irrefl, fun _ _ _ => pairReach_trans, pairReach_not_total⟩

end CSQIT_V1Bridge
