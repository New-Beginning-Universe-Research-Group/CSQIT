/- ================================================================================
CSQIT v12.1.2 — AxiomD/I/J 的层级诚实标注
文件: V12/Core/AxiomDerivation.lean
版本: v12.1.2
日期: 2026-07-30
================================================================================
从 AxiomA（因果复合）和 AxiomC（幺正振幅）出发：

  AxiomD（操作编织）→ W1 严格定理：自组合不动点唯一（有非平凡证明）
  AxiomI（信息因果性）→ W2 条件性定义：共识速率定义为光速 c(n)（定义性等同）
  AxiomJ（动力学演化）→ W2 条件性定理：8节点简化模型中单步迭代分歧为零

诚实标注（v12.1.0 深度自检修正）：
  - AxiomD：✅ W1 严格定理
           数学内容：自组合（α∘α=α）的不动点唯一
           概念偷换警示："编织操作收敛"是 W3 层命名，
             实际证明的是代数不动点性质，不是动力系统收敛
  - AxiomI：⚠️ W2 条件性定义
           不是从 AxiomA/C 推导的定理
           "共识速率 = 光速"是定义性等同，需要物理诠释假设
  - AxiomJ：⚠️ W2 条件性定理（8节点简化模型）
           数学证明本身严格，但模型假设是 W2 的：
             · 固定 8 个节点 = 特设选择
             · 单步完美收敛 = 高度理想化
             · 网络拓扑 = 全连接（隐含假设）
================================================================================ -/

import V12.Core.Foundation
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace CSQIT.V12.AxiomDerivation

open CSQIT.V12.Foundation

/-! ----------------------------------------------------------------------------
   AxiomD：自组合不动点（W1 严格定理）
   ----------------------------------------------------------------------------

  原始表述（W3 概念）：编织操作是收敛的，Weaver 网络最终达成共识。

  W1 严格形式化（数学内容）：
    - 从 AxiomC 的单射振幅和幺正性出发
    - 定义自组合不动点方程：α∘α = α
    - 证明：满足该方程的 α 唯一

  证明的非平凡性：
    - 利用单位模复数中 z² = z ⇒ z = 1（需排除 z = 0）
    - 再由单射性得不动点唯一

  诚实边界（W3 概念 → W1 数学的对应关系）：
    - "编织操作收敛" ↔ "自组合不动点唯一"
    - 这个对应是概念性命名，不是数学推导
    - 不动点唯一性 ≠ 动力系统收敛性证明
  ---------------------------------------------------------------------------- -/

/-- **W1 严格：自组合不动点**。
    α 是自组合不动点，当且仅当 α 与自身组合仍为 α。
    W3 概念命名：也称为"编织操作的不动点"。 -/
def weave_fixed_point {M C : Type*} [A : AxiomA M C] (α : C) : Prop :=
  A.compose α α = α

/-- **定理：自组合不动点唯一**（W1 严格）。
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
   AxiomI：信息因果性（W2 条件性定义，非推导）
   ----------------------------------------------------------------------------

  原始表述（W3 概念）：信息传播速率受限于光速。

  v12.1.0 诚实标注：
    - 共识传播速率 定义为 光速函数 c(n)
    - 这不是从 AxiomA/C 推导出来的定理
    - 而是将信息因果性作为定义引入框架（W2 条件性）
    - 其合理性来自射影尺度导数的物理诠释（W3 层）
  ---------------------------------------------------------------------------- -/

/-- **W2 条件性定义：共识传播速率**。
    定义为射影尺度的导数，即光速函数 c(n)。

    注意：这是定义，不是从 AxiomA/C 推导的定理。
    W2 条件：将此速率等同于"信息传播速率"需要物理假设。 -/
noncomputable def consensus_propagation_rate (n : ℕ) : ℝ := speedOfLight n

/-- **定理：共识传播速率非递增**（W1 严格数学性质 / W2 条件性物理解释）。
    数学证明：由 speedOfLight_strictAnti 定理，c(n) 严格递减。
    W2 条件：将此性质诠释为"信息因果性"需要物理假设。 -/
theorem consensus_rate_nonincreasing (n : ℕ) :
    consensus_propagation_rate (n + 1) ≤ consensus_propagation_rate n := by
  have h : n < n + 1 := by omega
  exact (speedOfLight_strictAnti h).le

/-! ----------------------------------------------------------------------------
   AxiomJ：动力学演化（W2 条件性定理，8节点简化模型）
   ----------------------------------------------------------------------------

  原始表述（W3 概念）：宇宙的演化是共识迭代的过程。

  W2 条件性形式化：
    - 定义共识迭代算子（每个节点与所有其他节点编织一次）
    - 证明：8节点全连接网络中，单步迭代后所有节点振幅相同
    - 因此：分歧（标准差）从非负值降为零

  W2 模型假设（不是从 AxiomA/C 推导的）：
    · 固定 8 个节点 = 特设网络大小选择
    · 全连接拓扑 = 特设网络结构选择
    · 单步完美收敛 = 高度理想化（无噪声、无损）
    · 节点 = 编织规则 = 概念对应（W3）

  数学证明本身（在给定模型假设下）是 W1 严格的。
  ---------------------------------------------------------------------------- -/

/-- **W2 条件性定义：共识分歧**（8节点模型）。
    定义为网络中节点相位的标准差。
    W2 条件：8 个节点是特设选择，不是从公理推导的。 -/
noncomputable def consensus_discrepancy {M C : Type*} [AxiomA M C] [Cx : AxiomC M C]
    (net : Fin 8 → C) : ℝ :=
  let avg_phase := (∑ i, Complex.arg (Cx.amplitude (net i))) / 8
  Real.sqrt ((∑ i, (Complex.arg (Cx.amplitude (net i)) - avg_phase) ^ 2) / 8)

/-- **W2 条件性定义：共识迭代算子**（8节点全连接模型）。
    单步迭代：每个节点与所有其他节点编织。
    使用 List.foldl 遍历除 i 外的所有节点。
    标注 noncomputable 因 Finset.toList 是非可计算。

    W2 条件：
      · 8 节点 = 特设选择
      · 全连接 = 特设拓扑
      · 单步迭代 = 特设动力学规则 -/
noncomputable def consensus_iterate {M C : Type*} [A : AxiomA M C]
    (net : Fin 8 → C) : Fin 8 → C :=
  fun i => (Finset.univ.erase i).toList.foldl (fun acc j => A.compose acc (net j)) (net i)

/-- **W1 严格定义：网络中所有节点振幅的乘积**。
    这是迭代后每个节点振幅的目标值。
    数学定义本身与模型假设无关。 -/
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

/-- **定理：共识分歧非递增**（W2 条件性定理，8节点模型）。
    数学证明（W1 严格）：迭代后所有节点的振幅相同，因此相位相同，方差为零。
    零 ≤ 任何非负数，故分歧非递增。

    W2 条件：结论依赖于 8 节点全连接单步迭代的模型假设。 -/
theorem consensus_discrepancy_nonincreasing {M C : Type*} [AxiomA M C] [Cx : AxiomC M C]
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
