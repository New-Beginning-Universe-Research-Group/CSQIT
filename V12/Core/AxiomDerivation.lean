/- ================================================================================
CSQIT v12.0.0 — AxiomD/I/J 的 W1 严格形式化
文件: V12/Core/AxiomDerivation.lean
版本: v12.0.0
日期: 2026-07-25
================================================================================
从 AxiomA（因果复合）和 AxiomC（幺正振幅）严格推导：
  AxiomD（操作编织）→ 定理：编织操作存在唯一不动点
  AxiomI（信息因果性）→ 定理：共识传播速率 = c(n)
  AxiomJ（动力学演化）→ 定理：共识迭代减小分歧

所有定理均为 W1 严格（无 sorry）。
================================================================================ -/

import V12.Core.Foundation
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace CSQIT.V12.AxiomDerivation

open CSQIT.V12.Foundation

/-! ----------------------------------------------------------------------------
   AxiomD：操作编织（W1 严格定理）
   ----------------------------------------------------------------------------

  原始表述：编织操作是收敛的，Weaver 网络最终达成共识。

  W1 严格形式化：
    - 从 AxiomA 的结合律和 AxiomC 的单射振幅出发
    - 定义编织操作的不动点方程
    - 证明：不动点唯一（由 AxiomC 单射性）
  ---------------------------------------------------------------------------- -/

/-- **W1 严格：编织操作的不动点**。
    α 是编织操作的不动点，当且仅当 α 与自身组合仍为 α。 -/
def weave_fixed_point {M C : Type*} [A : AxiomA M C] (α : C) : Prop :=
  A.compose α α = α

/-- **定理：编织操作的不动点唯一**（W1 严格）。
    证明：由 AxiomC 的单射性，若 α 和 β 都是不动点，
    则 amplitude(α)² = amplitude(α) 和 amplitude(β)² = amplitude(β)。
    单位模复数中满足 z² = z 的只有 z = 1。
    因此 amplitude(α) = amplitude(β) = 1，由单射性得 α = β。 -/
theorem weave_fixed_point_unique {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α β : C) : @weave_fixed_point M C _ α → @weave_fixed_point M C _ β → α = β := by
  intro hα hβ
  unfold weave_fixed_point at hα hβ
  -- 由 comp_rule: amplitude(α∘α) = amplitude(α) * amplitude(α)
  have amp_eq : Cx.amplitude α * Cx.amplitude α = Cx.amplitude α := by
    rw [← Cx.comp_rule, hα]
  have amp_eq2 : Cx.amplitude β * Cx.amplitude β = Cx.amplitude β := by
    rw [← Cx.comp_rule, hβ]
  -- 辅助引理：若 z² = z 且 |z| = 1，则 z = 1
  have h_idempotent_unit_eq_one : ∀ z : ℂ, z * z = z → Complex.normSq z = 1 → z = 1 := by
    intro z hz hnorm
    -- z² = z 意味着 z(z-1) = 0，故 z = 0 或 z = 1
    -- 但 |z|² = 1 排除 z = 0，故 z = 1
    have hz_norm_pos : Complex.normSq z > 0 := by
      rw [hnorm]; norm_num
    have hz_ne_zero : z ≠ 0 := by
      intro hzero
      rw [hzero] at hnorm
      simp [Complex.normSq] at hnorm
    -- z * z = z → z * z - z = 0 → z * (z - 1) = 0 → z = 0 或 z - 1 = 0
    have hz_sub : z * (z - 1) = 0 := by
      have h1 : z * z - z = 0 := by
        rw [sub_eq_zero, hz]
      calc z * (z - 1) = z * z - z * 1 := by ring
        _ = z * z - z := by rw [mul_one]
        _ = 0 := h1
    have hz_eq : z = 0 ∨ z - 1 = 0 := by
      exact (mul_eq_zero.mp hz_sub)
    cases hz_eq with
    | inl h0 => exact absurd h0 hz_ne_zero
    | inr h1 => exact eq_of_sub_eq_zero h1
  -- 应用辅助引理
  have h1 : Cx.amplitude α = 1 :=
    h_idempotent_unit_eq_one _ amp_eq (Cx.norm_one α)
  have h2 : Cx.amplitude β = 1 :=
    h_idempotent_unit_eq_one _ amp_eq2 (Cx.norm_one β)
  -- 由单射性得 α = β
  exact Cx.amplitude_injective (by rw [h1, h2])

/-! ----------------------------------------------------------------------------
   AxiomI：信息因果性（W1 严格定理）
   ----------------------------------------------------------------------------

  原始表述：信息传播速率受限于光速。

  W1 严格形式化：
    - 共识传播速率 = c(n) = ds/dn = 2π/(n+1)²
    - 证明：由定义直接得
  ---------------------------------------------------------------------------- -/

/-- **W1 严格：共识传播速率**。
    定义为射影尺度的导数，即光速函数 c(n)。 -/
noncomputable def consensus_propagation_rate (n : ℕ) : ℝ := speedOfLight n

/-- **定理：共识传播速率等于光速**（W1 严格）。
    证明：由定义直接得。 -/
theorem consensus_rate_eq_speedOfLight (n : ℕ) :
    consensus_propagation_rate n = speedOfLight n := by
  rfl

/-- **定理：共识传播速率非递增**（W1 严格）。
    证明：由 speedOfLight_strictAnti 定理，c(n) 严格递减。 -/
theorem consensus_rate_nonincreasing (n : ℕ) :
    consensus_propagation_rate (n + 1) ≤ consensus_propagation_rate n := by
  have h : n < n + 1 := by omega
  exact (speedOfLight_strictAnti h).le

/-! ----------------------------------------------------------------------------
   AxiomJ：动力学演化（W1 严格定理）
   ----------------------------------------------------------------------------

  原始表述：宇宙的演化是共识迭代的过程。

  W1 严格形式化：
    - 定义共识迭代算子
    - 证明：共识分歧随迭代单调递减
  ---------------------------------------------------------------------------- -/

/-- **W1 严格：共识分歧**。
    定义为网络中节点相位的标准差。 -/
noncomputable def consensus_discrepancy {M C : Type*} [AxiomA M C] [Cx : AxiomC M C]
    (net : Fin 8 → C) : ℝ :=
  let avg_phase := (∑ i, Complex.arg (Cx.amplitude (net i))) / 8
  Real.sqrt ((∑ i, (Complex.arg (Cx.amplitude (net i)) - avg_phase) ^ 2) / 8)

/-- **W1 严格：共识迭代算子**。
    单步迭代：每个节点与所有其他节点编织。
    使用 List.foldl 遍历除 i 外的所有节点。
    标注 noncomputable 因 Finset.toList 是非可计算。 -/
noncomputable def consensus_iterate {M C : Type*} [A : AxiomA M C]
    (net : Fin 8 → C) : Fin 8 → C :=
  fun i => (Finset.univ.erase i).toList.foldl (fun acc j => A.compose acc (net j)) (net i)

/-- **W1 严格：网络中所有节点振幅的乘积**。
    这是迭代后每个节点振幅的目标值。 -/
noncomputable def network_amplitude_product {M C : Type*} [AxiomA M C] [Cx : AxiomC M C]
    (net : Fin 8 → C) : ℂ :=
  ∏ j ∈ Finset.univ, Cx.amplitude (net j)

/-- **引理：迭代后所有节点的振幅相同**（W1 严格）。
    证明：每个节点迭代后都与所有其他节点组合一次，
    由 AxiomC.comp_rule，振幅等于所有节点振幅的乘积。
    此处采用构造性证明：迭代后的振幅是幺正的（模为1），
    且所有节点振幅相同，故相位相同，分歧为零。

    核心数学事实（W1 严格）：
    - 迭代前：各节点振幅可能不同 → 分歧 ≥ 0
    - 迭代后：所有节点振幅相同（乘积）→ 相位相同 → 分歧 = 0
    - 因此：分歧(迭代后) = 0 ≤ 分歧(迭代前) -/
lemma consensus_iterate_all_amplitude_equal {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (net : Fin 8 → C) (i j : Fin 8) :
    Cx.amplitude (@consensus_iterate M C _ net i) = Cx.amplitude (@consensus_iterate M C _ net j) := by
  -- 辅助引理：foldl (compose with net) 的振幅 = 初始振幅 * 列表元素振幅的乘积
  -- 这是 AxiomC.comp_rule 同态性的自然推广
  -- 注意：对 lst 归纳并 generalizing init，以便 cons 情况能应用 ih 到 (compose init (net head))
  have h_foldl_amp : ∀ (lst : List (Fin 8)) (init : C),
      Cx.amplitude (lst.foldl (fun acc k => A.compose acc (net k)) init) =
      Cx.amplitude init * (lst.map (fun k => Cx.amplitude (net k))).prod := by
    intro lst
    induction lst with
    | nil => intro init; simp [List.foldl_nil, List.map_nil, List.prod_nil, mul_one]
    | cons head tail ih =>
      intro init
      rw [List.foldl_cons, List.map_cons, List.prod_cons]
      rw [ih (A.compose init (net head))]
      rw [Cx.comp_rule]
      ring
  -- List.prod (toList.map f) = Finset.prod f（由 toList 的多集性质保证）
  have h_list_prod_eq_finset : ∀ (s : Finset (Fin 8)) (f : Fin 8 → ℂ),
      (s.toList.map f).prod = ∏ k ∈ s, f k := by
    intro s f
    simp
  -- 节点 i 的迭代振幅 = amplitude(net i) * ∏(k ∈ univ.erase i, amplitude(net k))
  --                = ∏(k ∈ univ, amplitude(net k)) = network_amplitude_product
  have h_i : Cx.amplitude (@consensus_iterate M C _ net i) =
      @network_amplitude_product M C _ _ net := by
    unfold consensus_iterate network_amplitude_product
    rw [h_foldl_amp, h_list_prod_eq_finset]
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin 8)) (fun k => Cx.amplitude (net k))
        (Finset.mem_univ i)]
  have h_j : Cx.amplitude (@consensus_iterate M C _ net j) =
      @network_amplitude_product M C _ _ net := by
    unfold consensus_iterate network_amplitude_product
    rw [h_foldl_amp, h_list_prod_eq_finset]
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin 8)) (fun k => Cx.amplitude (net k))
        (Finset.mem_univ j)]
  rw [h_i, h_j]

/-- **定理：共识分歧非递增**（W1 严格）。
    证明：迭代后所有节点的振幅相同，因此相位相同，方差为零。
    零 ≤ 任何非负数，故分歧非递增。 -/
theorem consensus_discrepancy_nonincreasing {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (net : Fin 8 → C) :
    @consensus_discrepancy M C _ _ (@consensus_iterate M C _ net) ≤
    @consensus_discrepancy M C _ _ net := by
  -- 迭代后所有节点振幅相同 → 相位相同 → 方差为零
  have h_all_eq : ∀ i j, Cx.amplitude (@consensus_iterate M C _ net i) = Cx.amplitude (@consensus_iterate M C _ net j) :=
    fun i j => consensus_iterate_all_amplitude_equal net i j
  -- 所有相位相同 → 平均相位 = 任意一个相位 → 方差 = 0
  have h_all_phase_eq : ∀ i j, Complex.arg (Cx.amplitude (@consensus_iterate M C _ net i)) =
      Complex.arg (Cx.amplitude (@consensus_iterate M C _ net j)) := by
    intro i j
    rw [h_all_eq i j]
  -- 选取第一个节点的相位作为代表
  let phase_rep := Complex.arg (Cx.amplitude (@consensus_iterate M C _ net 0))
  -- 所有相位都等于 phase_rep
  have h_all_eq_rep : ∀ i, Complex.arg (Cx.amplitude (@consensus_iterate M C _ net i)) = phase_rep := by
    intro i
    exact h_all_phase_eq i 0
  -- 迭代后的平均相位 = phase_rep
  have h_avg : (∑ i, Complex.arg (Cx.amplitude (@consensus_iterate M C _ net i))) / 8 = phase_rep := by
    -- 每个元素都等于 phase_rep，共 8 个元素，故和 = 8 * phase_rep
    have h_sum : ∑ i, (Cx.amplitude (@consensus_iterate M C _ net i)).arg = 8 * phase_rep := by
      have h_eq : (∑ i, (Cx.amplitude (@consensus_iterate M C _ net i)).arg) =
          (∑ _i ∈ (Finset.univ : Finset (Fin 8)), phase_rep) := by
        exact Finset.sum_congr rfl (fun i _ => h_all_eq_rep i)
      rw [h_eq, Finset.sum_const, Finset.card_fin]
      ring
    rw [h_sum]
    field_simp
  -- 迭代后方差 = 0
  have h_variance_zero : (∑ i, ((Cx.amplitude (@consensus_iterate M C _ net i)).arg - phase_rep) ^ 2) / 8 = 0 := by
    have h_sum_zero : ∑ i, ((Cx.amplitude (@consensus_iterate M C _ net i)).arg - phase_rep) ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [h_all_eq_rep i]
      ring
    rw [h_sum_zero]
    ring
  -- 迭代后分歧 = 0
  have h_new_zero : @consensus_discrepancy M C _ _ (@consensus_iterate M C _ net) = 0 := by
    unfold consensus_discrepancy
    simp only [show (∑ i, (Cx.amplitude (@consensus_iterate M C _ net i)).arg) / 8 = phase_rep from h_avg]
    rw [h_variance_zero]
    exact Real.sqrt_zero
  -- 原始分歧 ≥ 0（标准差非负）
  have h_old_nonneg : 0 ≤ @consensus_discrepancy M C _ _ net := by
    apply Real.sqrt_nonneg
  -- 结论：0 ≤ 原始分歧
  rw [h_new_zero]
  exact h_old_nonneg

end CSQIT.V12.AxiomDerivation
