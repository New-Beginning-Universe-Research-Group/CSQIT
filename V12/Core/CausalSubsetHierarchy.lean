/- ================================================================================
CSQIT v12.8.1 — CausalSubsetHierarchy：因果子集族的偏序/交半格结构
文件: V12/Core/CausalSubsetHierarchy.lean
版本: v12.8.1（从线性三层 → 层级偏序集的深化）

核心洞察（DeepShare + 用户）：
  "每一个稳定层级都只是一个子集，它与全集有共性但它不可能是全集，
   子集间可能有交集，子集还可能有它的子集。"
  
  用户的四条结构性断言：
  (1) S ⊆ M（子集性）
  (2) S ⊊ M（非全集性）
  (3) S₁ ∩ S₂ ≠ ∅ 可能（交集存在）
  (4) S' ⊊ S（子集还可能有子集）
  
  这刻画的不是线性层级，而是**偏序集（poset）** 结构——
  甚至可能是树状/网（DAG）结构。

三层有限性的严格区分：
  ┌──────────────────┬──────────┬────────────────────────────────────┐
  │ 有限性类型        │ 状态     │ 基础                                 │
  ├──────────────────┼──────────┼────────────────────────────────────┤
  │ 深度有限（级数）  │ ✅ W1 可证│ 格距非零 + 良基性（无无限下降链）    │
  │ 宽度有限（分支）  │ ❓ 待探索│ 因果子集族的结构性质                 │
  │ 内容有限（元素）  │ ❓ 待探索│ 归纳于深度 + 基座层有限              │
  │ 整体有限          │ ❌ 可能无限│ 反模型 M = ℝ 存在                   │
  └──────────────────┴──────────┴────────────────────────────────────┘

数学基础（W1 严格）：
  Foundation.CausalLattice M extends Lattice M
  → ⊔（sup）和 ⊓（inf）存在
  → 交半格结构可证

诚实边界：
  ✅ 纯 W1 严格工作——仅依赖 CausalLattice 的格结构
  ✅ 不引入新公理
  ✅ 零 sorry / 零 admit
================================================================================ -/

import V12.Core.Foundation

namespace CSQIT.V12.CausalSubsetHierarchy

open CSQIT.V12.Foundation

/-! ═══════════════════════════════════════════════════════════
   §1 因果子集的定义与基本性质（W1 严格）
   
   因果区间 = { z : M | x ≤ z ∧ z ≤ y }
   在 CausalLattice M 中，因果区间自身就是最基础的因果子集。
   
   层级：✅ W1 严格定义
   ═══════════════════════════════════════════════════════════ -/

/-- **因果区间**：[x, y] = { z : M | x ≤ z ∧ z ≤ y }
    
    这是最基础的因果子集定义。 -/
def causalInterval (M : Type*) [PartialOrder M] (x y : M) : Set M :=
  { z : M | x ≤ z ∧ z ≤ y }

/-- **因果区间的单调性**（W1 严格）：
    如果 x₁ ≤ x₂ 且 y₂ ≤ y₁，
    那么 [x₂, y₂] ⊆ [x₁, y₁]。
    
    证明：z ∈ [x₂, y₂] → x₂ ≤ z ≤ y₂
          → x₁ ≤ x₂ ≤ z ≤ y₂ ≤ y₁ → z ∈ [x₁, y₁] -/
theorem causalInterval_mono {M : Type*} [PartialOrder M]
    {x₁ x₂ y₁ y₂ : M} 
    (hx : x₁ ≤ x₂) (hy : y₂ ≤ y₁) :
    causalInterval M x₂ y₂ ⊆ causalInterval M x₁ y₁ := by
  intro z hz
  have h1 : x₂ ≤ z := hz.1
  have h2 : z ≤ y₂ := hz.2
  exact ⟨le_trans hx h1, le_trans h2 hy⟩

/-- **非退化因果区间非空**（W1 严格）：
    如果 x ≤ y，那么 x ∈ [x, y]。
    
    （对称性同理可得 y ∈ [x, y]。） -/
theorem causalInterval_nonempty_left {M : Type*} [PartialOrder M]
    {x y : M} (h : x ≤ y) :
    x ∈ causalInterval M x y := by
  have h1 : x ≤ x := le_refl x
  exact Set.mem_setOf_eq.mpr ⟨h1, h⟩

theorem causalInterval_nonempty_right {M : Type*} [PartialOrder M]
    {x y : M} (h : x ≤ y) :
    y ∈ causalInterval M x y := by
  have h1 : y ≤ y := le_refl y
  exact Set.mem_setOf_eq.mpr ⟨h, h1⟩

/-! ═══════════════════════════════════════════════════════════
   §2 ★★★ 因果子集的交半格结构（W1 严格，需要 Lattice）
   
   核心定理：两个因果区间的交**仍是**因果区间。
   
   证明思路（需要 Lattice 结构，⊔ = sup, ⊓ = inf）：
     causalInterval M x₁ y₁ ∩ causalInterval M x₂ y₂
   = causalInterval M (x₁ ⊔ x₂) (y₁ ⊓ y₂)
   
     z ∈ 左边
     ↔ (x₁≤z ∧ z≤y₁) ∧ (x₂≤z ∧ z≤y₂)
     ↔ (x₁≤z ∧ x₂≤z) ∧ (z≤y₁ ∧ z≤y₂)
     ↔ x₁⊔x₂ ≤ z ∧ z ≤ y₁⊓y₂    ← Lattice 的 sup/inf 性质
     ↔ z ∈ 右边
   
   关键约束：交非空当且仅当 x₁⊔x₂ ≤ y₁⊓y₂。
   
   这就是 CausalSubsetFamily M 上**交半格**的精确形式化：
     - 交集封闭（存在 ⊔ 和 ⊓）
     - 并集**不一定**封闭（可能不连通，诚实声明）
   
   层级：✅ W1 严格（仅 Lattice 结构）
   ═══════════════════════════════════════════════════════════ -/

/-- **★ 交半格定理**：两个因果区间的交等于 [x₁ ⊔ x₂, y₁ ⊓ y₂]（W1 严格）。
    
    在 Lattice M 中：
      causalInterval M x₁ y₁ ∩ causalInterval M x₂ y₂
    = causalInterval M (x₁ ⊔ x₂) (y₁ ⊓ y₂)
    
    这就是 DeepShare 洞察的精确 W1 严格形式化：
      "子集间可能有交集" ✓ （格结构保证）
      "每个稳定层级都只是一个子集" ✓ （定义保证）
      "子集还可能有子集" ✓ （嵌套在同一个偏序中） -/
theorem causalInterval_inter_eq_inf {M : Type*} [Lattice M]
    {x₁ y₁ x₂ y₂ : M} :
    causalInterval M x₁ y₁ ∩ causalInterval M x₂ y₂ =
    causalInterval M (x₁ ⊔ x₂) (y₁ ⊓ y₂) := by
  ext z
  simp only [causalInterval, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · -- → 方向：z ∈ [x₁,y₁] ∩ [x₂,y₂] → z ∈ [x₁⊔x₂, y₁⊓y₂]
    intro ⟨⟨hx₁, hy₁⟩, ⟨hx₂, hy₂⟩⟩
    have h_sup : x₁ ⊔ x₂ ≤ z := sup_le hx₁ hx₂
    have h_inf : z ≤ y₁ ⊓ y₂ := le_inf hy₁ hy₂
    exact ⟨h_sup, h_inf⟩
  · -- ← 方向：z ∈ [x₁⊔x₂, y₁⊓y₂] → z ∈ [x₁,y₁] ∩ [x₂,y₂]
    intro ⟨h_sup_le_z, h_z_le_inf⟩
    have hx₁ : x₁ ≤ x₁ ⊔ x₂ := le_sup_left
    have hx₂ : x₂ ≤ x₁ ⊔ x₂ := le_sup_right
    have hy₁ : y₁ ⊓ y₂ ≤ y₁ := inf_le_left
    have hy₂ : y₁ ⊓ y₂ ≤ y₂ := inf_le_right
    have h_x1_z : x₁ ≤ z := le_trans hx₁ h_sup_le_z
    have h_x2_z : x₂ ≤ z := le_trans hx₂ h_sup_le_z
    have h_z_y1 : z ≤ y₁ := le_trans h_z_le_inf hy₁
    have h_z_y2 : z ≤ y₂ := le_trans h_z_le_inf hy₂
    exact ⟨⟨h_x1_z, h_z_y1⟩, ⟨h_x2_z, h_z_y2⟩⟩

/-- **交非空当且仅当 x₁⊔x₂ ≤ y₁⊓y₂**（W1 严格）。
    
    这给出了两个因果区间有非空交集的精确判据。
    
    证明：
      Nonempty (S₁ ∩ S₂)
      ↔ ∃ z, z ∈ S₁ ∩ S₂
      ↔ ∃ z, x₁⊔x₂ ≤ z ∧ z ≤ y₁⊓y₂   （由交半格定理）
      ↔ x₁⊔x₂ ≤ y₁⊓y₂                 （令 z = x₁⊔x₂） -/
theorem causalInterval_inter_nonempty_iff {M : Type*} [Lattice M]
    {x₁ y₁ x₂ y₂ : M} :
    Set.Nonempty (causalInterval M x₁ y₁ ∩ causalInterval M x₂ y₂) ↔
    x₁ ⊔ x₂ ≤ y₁ ⊓ y₂ := by
  have h_eq : causalInterval M x₁ y₁ ∩ causalInterval M x₂ y₂ =
      causalInterval M (x₁ ⊔ x₂) (y₁ ⊓ y₂) :=
    causalInterval_inter_eq_inf
  rw [h_eq]
  constructor
  · -- → 方向：假设 [x₁⊔x₂, y₁⊓y₂] 非空，证明 x₁⊔x₂ ≤ y₁⊓y₂
    intro h
    rcases h with ⟨z, hz⟩
    have hz' : z ∈ causalInterval M (x₁ ⊔ x₂) (y₁ ⊓ y₂) := hz
    rcases hz' with ⟨h_sup, h_inf⟩
    exact le_trans h_sup h_inf
  · -- ← 方向：假设 x₁⊔x₂ ≤ y₁⊓y₂，构造非空
    intro h_le
    have h_x_in : x₁ ⊔ x₂ ∈ causalInterval M (x₁ ⊔ x₂) (y₁ ⊓ y₂) := by
      exact Set.mem_setOf_eq.mpr ⟨le_refl (x₁ ⊔ x₂), h_le⟩
    exact ⟨x₁ ⊔ x₂, h_x_in⟩

/-! ═══════════════════════════════════════════════════════════
   §3 嵌套因果区间的性质（W1 严格，PartialOrder）
   
   在偏序集 M 中，嵌套因果区间链：
     [x₁, y₁] ⊇ [x₂, y₂] ⊇ [x₃, y₃] ⊇ ...
   
   满足：
     - 下界递增：x₁ ≤ x₂ ≤ x₃ ≤ ...
     - 上界递减：y₁ ≥ y₂ ≥ y₃ ≥ ...
   
   这是深度有限性的基础——在有限类型中，
   单调序列最终必稳定（鸽巢原理）。
   
   层级：✅ W1 严格
   ═══════════════════════════════════════════════════════════ -/

/-- **嵌套因果区间的边界运动**（W1 严格）。
    
    如果 [x₂, y₂] ⊆ [x₁, y₁]，
    那么 x₁ ≤ x₂（下界递增）且 y₂ ≤ y₁（上界递减）。
    
    证明：
      x₂ ∈ [x₂, y₂]（因果区间自包含）⊆ [x₁, y₁]
      → x₁ ≤ x₂
      y₂ ∈ [x₂, y₂] ⊆ [x₁, y₁]
      → y₂ ≤ y₁ -/
theorem nested_causal_interval_bounds {M : Type*} [PartialOrder M]
    {x₁ y₁ x₂ y₂ : M} 
    (h_incl : causalInterval M x₂ y₂ ⊆ causalInterval M x₁ y₁)
    (h_nonempty₂ : x₂ ≤ y₂) :
    x₁ ≤ x₂ ∧ y₂ ≤ y₁ := by
  have hx₂_in : x₂ ∈ causalInterval M x₂ y₂ := 
    causalInterval_nonempty_left h_nonempty₂
  have hy₂_in : y₂ ∈ causalInterval M x₂ y₂ :=
    causalInterval_nonempty_right h_nonempty₂
  have h1 : x₂ ∈ causalInterval M x₁ y₁ := h_incl hx₂_in
  have h2 : y₂ ∈ causalInterval M x₁ y₁ := h_incl hy₂_in
  exact ⟨h1.1, h2.2⟩

/-! ═══════════════════════════════════════════════════════════
   §4 诚实总结与进一步方向
   
   v12.8.1 已完成（W1 严格，零 sorry）：
   ✅ causalInterval 定义 + 单调性
   ✅ 非空性引理（左/右端点）
   ✅ ★ 交半格定理（两个因果区间的交 = [x₁⊔x₂, y₁⊓y₂]）
   ✅ 交非空判据（Set.Nonempty ↔ x₁⊔x₂ ≤ y₁⊓y₂）
   ✅ 嵌套区间边界运动（下界递增 + 上界递减）
   
   明确未完成（待探索，需新公理/新结构）：
   ❌ 有限覆盖定理（M 被有限多个因果子集覆盖）
   ❌ 分支数有限性（每个因果子集的子层级数量）
   ❌ 内容有限性（归纳于深度 + 基座层有限）
   ❌ 无限 M 情形下的深度有限性（需要良基性假设）
   
   千禧年 dissolve 链的潜在连接：
   如果能证明"有限覆盖 + 每个覆盖有限"，
   那么 BKM 积分有界 = 有限项有界项之和。
   这可能是千禧年难题溶解论证的真正核心。
   
   层级标记：
     本文模块所有 theorem = W1 严格
     零 sorry / 零 admit
   ═══════════════════════════════════════════════════════════ -/

end CSQIT.V12.CausalSubsetHierarchy
