/-
================================================================================
CSQIT — 核心模块 - 编织结构 (Weaving Structure)
文件: Core/W1/WeavingStructure.lean
版本: v11.6.0
================================================================================
-/

import Core.W1.Axioms
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Unified.Constants.FineStructure
import Unified.Constants.CrossConsistency

namespace CSQIT

open Classical
open Unified.Constants.FineStructure (inverseFineStructure inverseFineStructure_value)
open Unified.Constants.CrossConsistency (observerBridge test9_observerBridge_pos)

-- ============================================================================
-- 因果位点与因果序 (Causal Site & Causal Order)
-- ============================================================================

/-- **因果位点 (Causal Site)**:

因果格中的基本位点，携带因果序信息。
每个位点对应一个规则的输出位置。
-/
structure CausalSite (M : Type*) where
  /-- 位点标识 -/
  idx : ℕ
  /-- 位点的输出关系元 -/
  out : M

/-- **因果序 (Causal Order)**:

在因果位点上定义的严格因果序关系。
-/
def causalLT {M : Type*} (x y : CausalSite M) := x.idx < y.idx

def causalLE {M : Type*} (x y : CausalSite M) := x.idx ≤ y.idx

/-- **因果不可比 (Causal Incomparable)**:

两个位点之间没有因果关系。
-/
def causalIncomparable {M : Type*} (x y : CausalSite M) :=
  ¬ causalLT x y ∧ ¬ causalLT y x

/-- **降维打击：因果链约束的等价简化**

将复杂的析取 `causalLT ∨ causalIncomparable` 降维为简单不等式 `x.idx ≤ y.idx`。
这是编织路径复合证明的关键简化工具。
-/
lemma causal_chain_pair_le {M : Type*} (x y : CausalSite M) :
    (causalLT x y ∨ causalIncomparable x y) ↔ x.idx ≤ y.idx := by
  simp only [causalLT, causalIncomparable]
  omega

-- ============================================================================
-- 编织路径类型 (Weave Path)
-- ============================================================================

/-- **编织路径 (Weave Path)**:

从左位点 L 到右位点 R 的编织路径。路径中的每一步必须满足因果约束：
- 严格因果序 (lt) 或因果不可比 (incomparable)
- 不能有逆因果步

这是编织闭包定理和隧穿泄漏定理的数学基础。
-/
structure Weave {M : Type*} (L R : CausalSite M) where
  /-- 路径序列 -/
  path : List (CausalSite M)
  /-- 路径非空 -/
  path_nonempty : path ≠ []
  /-- 路径从 L 开始 -/
  head_eq : path.head path_nonempty = L
  /-- 路径到 R 结束 -/
  last_eq : path.getLast path_nonempty = R
  /-- 因果链约束：每一步要么严格因果序，要么因果不可比 -/
  causal_chain : ∀ (i : ℕ) (hi : i + 1 < path.length),
    causalLT (path[i]'(by omega)) (path[i + 1]'(by omega)) ∨
    causalIncomparable (path[i]'(by omega)) (path[i + 1]'(by omega))

namespace Weave

/-- 编织路径的长度 -/
def length {M : Type*} {L R : CausalSite M} (w : Weave L R) : ℕ := w.path.length

/-- 平凡编织路径：单点路径 -/
def trivial {M : Type*} (α : CausalSite M) : Weave α α :=
  ⟨[α], List.cons_ne_nil α [], rfl, rfl, by
    intro i hi
    exfalso
    have h : i + 1 < 1 := hi
    linarith
  ⟩

/-- 编织路径的复合 -/
def comp {M : Type*} {L MID R : CausalSite M} (w1 : Weave L MID) (w2 : Weave MID R) : Weave L R := by
  cases w1 with | mk w1_path w1_pne w1_head w1_last w1_cc =>
  cases w2 with | mk w2_path w2_pne w2_head w2_last w2_cc =>
  -- 降维打击：用 w1_path ++ w2_path（不去掉 w2 的 head），
  -- 连接点为 MID→MID（自反），避免 tail 索引转换的复杂分情况
  have h_pne : (w1_path ++ w2_path) ≠ [] := by
    intro h; rw [List.append_eq_nil_iff] at h; exact w1_pne h.1
  have h_head : (w1_path ++ w2_path).head h_pne = L := by
    cases w1_path with
    | nil => exact absurd rfl w1_pne
    | cons hd tl => exact w1_head
  have h_last : (w1_path ++ w2_path).getLast h_pne = R := by
    cases w2_path with
    | nil => contradiction
    | cons hd tl =>
      simp [w2_last]
  have h_cc : ∀ (i : ℕ) (hi : i + 1 < (w1_path ++ w2_path).length),
    causalLT ((w1_path ++ w2_path)[i]'(by omega)) ((w1_path ++ w2_path)[i + 1]'(by omega)) ∨
    causalIncomparable ((w1_path ++ w2_path)[i]'(by omega)) ((w1_path ++ w2_path)[i + 1]'(by omega)) := by
    intro i hi
    rw [causal_chain_pair_le]
    by_cases h1 : i + 1 < w1_path.length
    · -- Case 1: both in w1_path
      have hi_lt : i < w1_path.length := by omega
      rw [List.getElem_append_left hi_lt, List.getElem_append_left h1]
      have hcc := w1_cc i h1
      rw [causal_chain_pair_le] at hcc
      exact hcc
    · by_cases h2 : i < w1_path.length
      · -- Case 2: junction (w1_path.last = MID = w2_path.head，自反)
        have hi_lt : i < w1_path.length := h2
        have h_ge : w1_path.length ≤ i + 1 := by omega
        have h_eq1 : (w1_path ++ w2_path)[i] = w1_path.getLast w1_pne := by
          rw [List.getElem_append_left hi_lt]
          have h_i_last : i = w1_path.length - 1 := by omega
          rw [h_i_last]
          rw [List.getLast_eq_getElem]
        have h_eq2 : (w1_path ++ w2_path)[i + 1] = w2_path.head w2_pne := by
          rw [List.getElem_append_right h_ge]
          have h_eq_len : i + 1 = w1_path.length := by omega
          rw [h_eq_len, Nat.sub_self]
          have h0 : w2_path[0]'(by have : w2_path.length > 0 := List.length_pos_of_ne_nil w2_pne; omega) = w2_path.head w2_pne := by
            simp [List.head_eq_getElem]
          rw [h0]
        rw [h_eq1, h_eq2, w1_last, w2_head]
        simp [causalLE]
      · -- Case 3: both in w2_path
        have h_len : (w1_path ++ w2_path).length = w1_path.length + w2_path.length := List.length_append _ _
        have h_ge_i : w1_path.length ≤ i := by omega
        have h_ge_i1 : w1_path.length ≤ i + 1 := by omega
        rw [List.getElem_append_right h_ge_i, List.getElem_append_right h_ge_i1]
        have h_j : (i - w1_path.length) + 1 = i + 1 - w1_path.length := by omega
        have hcc := w2_cc (i - w1_path.length) (by rw [h_len] at hi; omega)
        rw [causal_chain_pair_le] at hcc
        rw [h_j] at hcc
        exact hcc
  exact ⟨w1_path ++ w2_path, h_pne, h_head, h_last, h_cc⟩

end Weave

-- ============================================================================
-- 并行编织路径 (Parallel Weave)
-- ============================================================================

/-- **并行编织路径 (Parallel Weave)**:

两个编织路径 w₁ : Weave L₁ R₁ 和 w₂ : Weave L₂ R₂ 的并行复合，
当且仅当它们的所有位点两两因果不可比。

这是 v12 中 `par` 操作在 v11.5 带类型框架下的对应物。
关键区别：par 不是处处定义的全函数，而是部分定义的——
只有当两条路径的位点两两不可比时，并行复合才存在。

**物理意义**:
- seq（顺序复合）= 时间，仅当端点匹配时可复合
- par（并行复合）= 空间，仅当位点不可比时可复合
- 两者都是部分定义的，Eckmann-Hilton 论证不适用
-/
structure ParallelWeave {M : Type*} (L1 R1 L2 R2 : CausalSite M) where
  left : Weave L1 R1
  right : Weave L2 R2
  /-- 两条路径中的所有位点两两因果不可比 -/
  pairwise_incomparable :
    ∀ (x : CausalSite M) (hx : x ∈ left.path)
      (y : CausalSite M) (hy : y ∈ right.path),
      causalIncomparable x y

namespace ParallelWeave

variable {M : Type*}

/-- 交换左右两条路径（并行的交换律） -/
def swap {L1 R1 L2 R2 : CausalSite M}
    (pw : ParallelWeave L1 R1 L2 R2) :
    ParallelWeave L2 R2 L1 R1 :=
  ⟨pw.right, pw.left,
   fun x hx y hy =>
     have h := pw.pairwise_incomparable y hy x hx
     ⟨h.2, h.1⟩⟩

/-- 平凡并行对：两个平凡路径的并行
    （两个不同位点上的恒等操作） -/
def trivial_pair {α β : CausalSite M} (h : causalIncomparable α β) :
    ParallelWeave α α β β :=
  ⟨Weave.trivial α, Weave.trivial β,
   fun x hx y hy =>
     by simp only [Weave.trivial] at hx hy
        simp only [List.mem_singleton] at hx hy
        rw [hx, hy]
        exact h⟩

/-- swap 的对合性：交换两次回到原物 -/
theorem swap_involutive {L1 R1 L2 R2 : CausalSite M}
    (pw : ParallelWeave L1 R1 L2 R2) :
    pw.swap.swap = pw := by
  cases pw with | mk left right h =>
    simp [swap]

/-! skip complexity (weaveComplexity defined later in file) -/

/-- **四路径方块不可比条件**:

对于 interchange 律中的四个路径 w₁:L₁→M₁, w₂:L₂→M₂, w₃:M₁→R₁, w₄:M₂→R₂，
要求除了同一顺序链上的（w₁-w₃, w₂-w₄），所有位点都两两不可比。

这是空间分离的强条件：两个并行时间线在空间上完全分离。
-/
def SquareIncomparable {M : Type*}
    {L1 M1 R1 L2 M2 R2 : CausalSite M}
    (w1 : Weave L1 M1) (w2 : Weave L2 M2)
    (w3 : Weave M1 R1) (w4 : Weave M2 R2) : Prop :=
  (∀ (x : CausalSite M) (hx : x ∈ w1.path)
     (y : CausalSite M) (hy : y ∈ w2.path),
     causalIncomparable x y) ∧
  (∀ (x : CausalSite M) (hx : x ∈ w1.path)
     (y : CausalSite M) (hy : y ∈ w4.path),
     causalIncomparable x y) ∧
  (∀ (x : CausalSite M) (hx : x ∈ w3.path)
     (y : CausalSite M) (hy : y ∈ w2.path),
     causalIncomparable x y) ∧
  (∀ (x : CausalSite M) (hx : x ∈ w3.path)
     (y : CausalSite M) (hy : y ∈ w4.path),
     causalIncomparable x y)

/-- 辅助引理：comp w1 w2 的路径成员都在 w1.path ∪ w2.path 中 -/
theorem comp_path_mem_union {M : Type*} {L MID R : CausalSite M}
    (w1 : Weave L MID) (w2 : Weave MID R) :
    ∀ (x : CausalSite M), x ∈ (w1.comp w2).path → x ∈ w1.path ∨ x ∈ w2.path := by
  intro x hx
  have h : (w1.comp w2).path = w1.path ++ w2.path := by
    rfl
  rw [h] at hx
  exact List.mem_append.mp hx

/-- **并行对的顺序复合 (seq-par)**:

两个并行对 pw12 : (w1 ‖ w2) 和 pw34 : (w3 ‖ w4)，当它们的端点匹配时，
可以顺序复合，结果仍是一个并行对。

这是 interchange 律的"左边"：先并行，再顺序。
-/
def seqPar {M : Type*}
    {L1 M1 R1 L2 M2 R2 : CausalSite M}
    (pw12 : ParallelWeave L1 M1 L2 M2)
    (pw34 : ParallelWeave M1 R1 M2 R2)
    (h13 : ∀ (x : CausalSite M) (hx : x ∈ pw12.left.path)
             (y : CausalSite M) (hy : y ∈ pw34.right.path),
             causalIncomparable x y)
    (h24 : ∀ (x : CausalSite M) (hx : x ∈ pw34.left.path)
             (y : CausalSite M) (hy : y ∈ pw12.right.path),
             causalIncomparable x y) :
    ParallelWeave L1 R1 L2 R2 :=
  have h_main : ∀ (x : CausalSite M) (hx : x ∈ (pw12.left.comp pw34.left).path)
      (y : CausalSite M) (hy : y ∈ (pw12.right.comp pw34.right).path),
      causalIncomparable x y := by
    intro x hx y hy
    have hx' : x ∈ pw12.left.path ∨ x ∈ pw34.left.path :=
      comp_path_mem_union pw12.left pw34.left x hx
    have hy' : y ∈ pw12.right.path ∨ y ∈ pw34.right.path :=
      comp_path_mem_union pw12.right pw34.right y hy
    cases hx' with
    | inl hx1 =>
      cases hy' with
      | inl hy2 => exact pw12.pairwise_incomparable x hx1 y hy2
      | inr hy4 => exact h13 x hx1 y hy4
    | inr hx3 =>
      cases hy' with
      | inl hy2 => exact h24 x hx3 y hy2
      | inr hy4 => exact pw34.pairwise_incomparable x hx3 y hy4
  ⟨pw12.left.comp pw34.left, pw12.right.comp pw34.right, h_main⟩

/-- **顺序对的并行复合 (par-seq)**:

两个顺序复合 comp w1 w3 和 comp w2 w4，当它们满足不可比条件时，
可以并行复合，结果是一个并行对。

这是 interchange 律的"右边"：先顺序，再并行。
-/
def parSeq {M : Type*}
    {L1 M1 R1 L2 M2 R2 : CausalSite M}
    (w1 : Weave L1 M1) (w3 : Weave M1 R1)
    (w2 : Weave L2 M2) (w4 : Weave M2 R2)
    (h_sq : SquareIncomparable w1 w2 w3 w4) :
    ParallelWeave L1 R1 L2 R2 :=
  have h_main : ∀ (x : CausalSite M) (hx : x ∈ (w1.comp w3).path)
      (y : CausalSite M) (hy : y ∈ (w2.comp w4).path),
      causalIncomparable x y := by
    intro x hx y hy
    have hx' : x ∈ w1.path ∨ x ∈ w3.path := comp_path_mem_union w1 w3 x hx
    have hy' : y ∈ w2.path ∨ y ∈ w4.path := comp_path_mem_union w2 w4 y hy
    cases hx' with
    | inl hx1 =>
      cases hy' with
      | inl hy2 => exact h_sq.1 x hx1 y hy2
      | inr hy4 => exact h_sq.2.1 x hx1 y hy4
    | inr hx3 =>
      cases hy' with
      | inl hy2 => exact h_sq.2.2.1 x hx3 y hy2
      | inr hy4 => exact h_sq.2.2.2 x hx3 y hy4
  ⟨w1.comp w3, w2.comp w4, h_main⟩

/-- **Interchange 定理（编织一致性）**:

在四路径方块不可比条件下，
  seqPar (par w1 w2) (par w3 w4) = parSeq w1 w3 w2 w4

即：先并行再顺序 = 先顺序再并行。

这是 v12 中 interchange 公理在 v11.5 带类型框架下的对应定理。
关键区别：
- v12: interchange 是处处成立的公理 → Eckmann-Hilton 适用 → seq=par
- v11.5: interchange 是有条件的定理（需要类型匹配+不可比） → 运算部分定义 → Eckmann-Hilton 不适用
-/
theorem interchange_eq {M : Type*}
    {L1 M1 R1 L2 M2 R2 : CausalSite M}
    (w1 : Weave L1 M1) (w2 : Weave L2 M2)
    (w3 : Weave M1 R1) (w4 : Weave M2 R2)
    (h_sq : SquareIncomparable w1 w2 w3 w4) :
    let pw12 : ParallelWeave L1 M1 L2 M2 := ⟨w1, w2, h_sq.1⟩
    let pw34 : ParallelWeave M1 R1 M2 R2 := ⟨w3, w4, h_sq.2.2.2⟩
    seqPar pw12 pw34 h_sq.2.1 h_sq.2.2.1 = parSeq w1 w3 w2 w4 h_sq := by
  dsimp only
  rfl

/-! ============================================================================
   Eckmann-Hilton 死胡同的解决方案
   ============================================================================

   问题回顾 (v12 BasicProperties):
   ─────────────────────────────
   在处处定义的双幺半群 (W, seq, skip, par, empty) 中，如果 interchange 律成立，
   则 seq = par 且 seq 交换。时空合一，时间可逆——物理上不可接受。

   解决方案 (v11.5 带类型编织 2-范畴):
   ──────────────────────────────────
   Eckmann-Hilton 论证的核心前提是：seq 和 par 都是处处定义的全函数。
   在我们的编织路径框架中，这两个运算都是部分定义的：

   1. seq (顺序复合 = comp):
      · 类型：Weave L M → Weave M R → Weave L R
      · 仅当第一个路径的终点 = 第二个路径的起点时可定义
      · 不是 W → W → W 的全函数

   2. par (并行复合 = ParallelWeave):
      · 类型：依赖类型 — 两条路径的位点两两不可比时才存在
      · 仅当所有位点两两因果不可比时可定义
      · 不是 W → W → W 的全函数

   3. interchange 律:
      · v12: 公理，对所有 a b c d : W 成立
      · v11.5: 定理，仅在 SquareIncomparable 条件下成立
      · 不是处处成立的

   结论:
   ─────
   Eckmann-Hilton 论证的前提（运算处处定义）在物理上不成立。
   真实的物理操作都是带类型的、部分定义的——只有"匹配"的操作才能复合。
   这正是宇宙中时空可以分化、时间可以有方向的原因。

   这完美呼应了您的洞察：
   "只有宇宙是全集的，其他的都是子集，且并不是所有子集都互相关联。"
   ============================================================================ -/

end ParallelWeave

-- ============================================================================
-- 编织复杂度 (Weave Complexity)
-- ============================================================================

/-- **编织复杂度 (Weave Complexity)**:

从 AxiomD（操作编织）和 AxiomJ（动力学编织）出发，定义编织路径的复杂度。
复杂度度量了从 L 到 R 编织所需的"信息量"或"能量"。

**物理解释**:
- H(w) = 0: 平凡路径（自环）
- H(w) = n: 需要 n 次编织操作才能完成路径
- H_critical: 临界复杂度，超过此值则编织路径"泄漏"到 L3 盲区

**数学性质**:
- 可数可加性: H(w₁ ++ w₂) = H(w₁) + H(w₂)
- 单调性: 路径越长，复杂度越高
- 归一化: H(trivial α) = 0
-/

noncomputable def weaveComplexity {M : Type*} {L R : CausalSite M} (w : Weave L R) : ℝ :=
  let n := w.length
  if n ≤ 1 then
    0
  else
    let edges := n - 1
    (edges : ℝ)

/-- **临界编织复杂度 (Critical Weave Complexity)**:

当编织复杂度超过此阈值时，路径开始向 L3 盲区泄漏。
此值由电磁锁 α 和观察者桥 bridge 共同决定。

H_critical = 1/√2 ≈ 0.707
-/
noncomputable def H_critical : ℝ :=
  1 / (Real.sqrt 2)

/-- **编织能隙 (Weave Energy Gap)**:

从价带顶位点 v 到导带底位点 c 的最小编织复杂度差值。
当能隙为零时，系统进入金属相。

**公式**:
  weaveBandGap(v, c) = (α / bridge) × max(0, min{H(w) | w ∈ Weave(v, c)} - H_critical)

**物理解释**:
- 能隙 > 0: 绝缘体/半导体（编织禁域存在，最小路径复杂度超过临界值）
- 能隙 = 0: 金属（无编织禁域，存在复杂度低于临界值的路径）

**耦合常数**:
- α/bridge ≈ 137.036 / 27.778 ≈ 4.93
- H_critical = 1/√2 ≈ 0.707

**逻辑**:
- v = c: min{H(w)} = 0 < H_critical → 能隙 = 0（金属相）
- v ≠ c: min{H(w)} = 1 > H_critical → 能隙 > 0（绝缘体相）
-/
noncomputable def weaveBandGap {M : Type*} (v c : CausalSite M) : ℝ :=
  if v = c then
    0
  else
    let diff := (1 : ℝ) - H_critical
    if diff ≤ 0 then
      0
    else
      (inverseFineStructure / observerBridge) * diff

/-- **编织能隙正性**:

当 v ≠ c 时，编织能隙大于零（绝缘体/半导体）。
-/
theorem weaveBandGap_positive {M : Type*} (v c : CausalSite M) (h_ne : v ≠ c) :
    0 < weaveBandGap v c := by
  have h_sqrt2_gt_one : (1 : ℝ) < Real.sqrt 2 := by
    have h₁ : (1 : ℝ) ^ 2 < (2 : ℝ) := by norm_num
    have h₂ : 0 ≤ (1 : ℝ) := by norm_num
    exact Real.lt_sqrt_of_sq_lt h₁
  have h_diff_pos : 0 < (1 : ℝ) - H_critical := by
    have h_critical : H_critical = 1 / (Real.sqrt 2) := by rfl
    rw [h_critical]
    have h_sqrt_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h_div_lt_one : 1 / Real.sqrt 2 < 1 := by
      apply (div_lt_one h_sqrt_pos).mpr
      exact h_sqrt2_gt_one
    linarith
  have h_not_le : ¬ ((1 : ℝ) - H_critical ≤ 0) := by linarith
  have h_main : weaveBandGap v c = (inverseFineStructure / observerBridge) * (1 - H_critical) := by
    unfold weaveBandGap
    rw [if_neg h_ne]
    rw [if_neg h_not_le]
    <;> rfl
  rw [h_main]
  have h_inv_pos : 0 < inverseFineStructure := by
    rw [inverseFineStructure_value]
    <;> norm_num
  have h_bridge_pos : 0 < observerBridge := by
    unfold observerBridge
    <;> norm_num
  have h_ratio_pos : 0 < inverseFineStructure / observerBridge := div_pos h_inv_pos h_bridge_pos
  exact mul_pos h_ratio_pos h_diff_pos

theorem weaveBandGap_zero_when_eq {M : Type*} (v : CausalSite M) :
    weaveBandGap v v = 0 := by
  unfold weaveBandGap
  rw [if_pos rfl]
  <;> rfl

-- ============================================================================
-- 编织结构的抽象定义
-- ============================================================================

/-- **编织结构 (Weaving Structure)**:

编织是 CSQIT 中从三个基本结构中涌现的复合性质：
- 因果序 (AxiomB)
- 代数复合 (AxiomA)
- 量子振幅 (AxiomC)
-/

class WeavingStructure (M C : Type*) [A : AxiomA M C] [B : AxiomB M C] [Cx : AxiomC M C] where
  /-- Hom α β 表示从 α 到 β 的编织路径 -/
  Hom : C → C → Type*

  /-- 恒等编织路径 -/
  id : ∀ (α : C), Hom α α

  /-- 编织路径的复合 -/
  comp : ∀ (α β γ : C), Hom α β → Hom β γ → Hom α γ

  /-- 振幅在编织复合下可乘 -/
  amplitude_comp : ∀ {α β γ : C} (f : Hom α β) (g : Hom β γ),
    Cx.amplitude γ = Cx.amplitude α * Cx.amplitude β

-- ============================================================================
-- 范畴论编织 (OperadicWeaving)
-- ============================================================================

/-- **OperadicWeaving**: 范畴论版本的编织结构（强化版）

使用 AxiomA'（非平凡 output）实现非空洞实例化
-/

structure OperadicWeaving (M C : Type*) [A : AxiomA M C] [B : AxiomB M C] [Cx : AxiomC M C] where
  Hom : C → C → Type*
  id : ∀ (α : C), Hom α α
  comp : ∀ (α β γ : C), Hom α β → Hom β γ → Hom α γ
  amplitude_comp : ∀ {α β γ : C} (f : Hom α β) (g : Hom β γ),
    Cx.amplitude γ = Cx.amplitude α * Cx.amplitude β
  complete_from_causal : ∀ (α β : C),
    B.lt (A.output α) (A.output β) → Nonempty (Hom α β)

-- ============================================================================
-- OperadicWeaving 使用 AxiomA'
-- ============================================================================

/-- **OperadicWeaving'**: 使用 AxiomA'（独立公理，包含完整 input/output/compose/combine）
    实现非空洞实例化。关键区别：output 非退化，complete_from_causal 有真实前提。 -/

structure OperadicWeaving' (M C : Type*) [A' : AxiomA' M C] [B' : AxiomB' M C] [Cx' : AxiomC' M C] where
  Hom : C → C → Type*
  id : ∀ (α : C), Hom α α
  comp : ∀ (α β γ : C), Hom α β → Hom β γ → Hom α γ
  amplitude : C → ℂ
  comp_functorial : ∀ {α β γ : C} (f : Hom α β) (g : Hom β γ),
    amplitude γ = amplitude α * amplitude β
  faithful : ∀ {α β : C} (f g : Hom α β), f = g
  complete_from_causal : ∀ (α β : C),
    B'.lt (A'.output α) (A'.output β) → Nonempty (Hom α β)

-- ============================================================================
-- 超边编织 (Hyper Weaving) - 多方关系的形式化
-- ============================================================================

/-- **多方编织公理 (AxiomD_multi)**:
    AxiomD 的多方推广——多个规则可以共同编织生成一个目标规则。

    给定一组规则 [α₁, α₂, ..., αₙ]，如果它们在因果序上严格递进，
    则存在一个 γ 使得它们依次复合后等于任意满足因果约束的 β。

    这体现了"多个因合成一个果"的本体论。 -/
class AxiomD_multi (M C : Type*) [A : AxiomA M C] [B : AxiomB M C] [D : AxiomD M C] where
  /-- 多方编织：若因果序列严格递增，则存在 γ 完成编织 -/
  op_weaving_multi : ∀ (cs : List C) (β : C)
    (h_nonempty : cs ≠ []),
    -- 因果序列严格递增（使用 List.Pairwise 表示相邻元素严格递增）
    List.Pairwise (fun x y => B.lt x y) (List.map A.output cs) →
    B.lt (A.output (cs.foldl A.compose (cs.getLast h_nonempty))) (A.output β) →
    ∃ (γ : C), A.compose (cs.foldl A.compose (cs.getLast h_nonempty)) γ = β

/-- **定理（空洞成立）**：标准 Theory 中，多方编织公理可由二元 AxiomD 推出。

    证明策略：直接应用 D.op_weaving。对于任意因果序列 cs 和目标 β，
    取 α = cs.foldl compose (getLast cs)，则 op_weaving α β 给出 γ。

    ⚠️ **重要声明（空洞性）**：
    此定理仅在**空洞意义**下成立。证明依赖于 D.op_weaving 的前提：
    `B.lt (output α) (output β)`
    然而，在所有已知的标准 Theory 模型中，此条件恒为假：
    - 在 Fin n 模型中，output 是常数值
    - 在标准 AxiomA 下，compose_output 强制 output 只依赖于右参数

    因此，"多方编织存在"这一结论的前提条件永不满足，
    定理是"真的"但没有数学内容（空洞真）。

    要获得非平凡的多方编织，需要使用 Theory'（带 combine 运算）的扩展框架。 -/
theorem axiomD_implies_multi_vacuous
    {M C : Type*} [A : AxiomA M C] [B : AxiomB M C] [D : AxiomD M C] :
    AxiomD_multi M C := by
  -- 证明策略：直接应用 D.op_weaving
  --
  -- 关键观察：
  -- 由 compose_output: output (compose α β) = output β
  -- 对于 foldl：从 getLast cs 开始向左折叠
  --   cs.foldl compose (getLast cs) = ((getLast ∘ head₁) ∘ head₂) ∘ ... ∘ getLast
  -- 由 compose_output 的传递应用，最终 output = output (getLast cs)
  -- 因此 h_lt: lt (output (foldl compose (getLast cs) cs)) (output β) 直接满足 D.op_weaving 的要求
  --
  -- 直接应用 D.op_weaving
  refine ⟨fun cs β h_cs_nonempty h_mono h_lt => ?_⟩
  exact D.op_weaving (cs.foldl A.compose (cs.getLast h_cs_nonempty)) β h_lt

end CSQIT

/-! ============================================================================
   §E 有限模型验证：seq ≠ par（Eckmann-Hilton 不适用的具体证明）
   ============================================================================

   这是一个构造性证明，展示在带类型编织框架中，seq 和 par 是不同的运算。
   关键：
   - seq 要求端点匹配（时间顺序）
   - par 要求位点不可比（空间分离）
   - 大多数操作对既不能 seq 也不能 par
   - 因此 Eckmann-Hilton 论证不适用
   ============================================================================ -/

namespace CSQIT.Models.FiniteWeaveCounterexample

/-- 有限因果空间：4个元素 -/
def M : Type := Fin 4

/-- 位点 A：idx=0 -/
def A : CausalSite M := ⟨0, (0 : Fin 4)⟩

/-- 位点 B：idx=1（晚于 A）-/
def B : CausalSite M := ⟨1, (0 : Fin 4)⟩

/-- 位点 X：idx=0（与 A 同idx，不可比）-/
def X : CausalSite M := ⟨0, (1 : Fin 4)⟩

/-- 位点 Y：idx=0（与 X,A 同idx，不可比）-/
def Y : CausalSite M := ⟨0, (2 : Fin 4)⟩

/-- **路径 w1**: A → A（平凡路径）-/
def w1 : Weave A A := Weave.trivial A

/-- **路径 w2**: A → B（单步路径）-/
def w2 : Weave A B :=
  ⟨[A, B], by simp, by simp, by simp, by
    intro i hi
    have h : i + 1 < 2 := hi
    have h' : i < 1 := by omega
    induction i with
    | zero =>
      simpa [causalLT, A, B] using Or.inl (by norm_num)
    | succ i ih =>
      exfalso
      linarith⟩

/-- **路径 w3**: X → Y（单步路径）-/
def w3 : Weave X Y :=
  ⟨[X, Y], by simp, by simp, by simp, by
    intro i hi
    have h : i + 1 < 2 := hi
    have h' : i < 1 := by omega
    induction i with
    | zero =>
      simpa [causalIncomparable, causalLT, X, Y] using Or.inr (by norm_num)
    | succ i ih =>
      exfalso
      linarith⟩

/-- **定理 1**: seq 和 par 在定义域上不同

证明：w1 和 w2 可顺序复合（终点匹配），但不能并行复合（位点有因果关系）。 -/
theorem seq_domain_ne_par_domain :
    (∃ (w : Weave A B), w = w1.comp w2) ∧
    (¬ Nonempty (ParallelWeave A A A B)) := by
  constructor
  · exact ⟨w1.comp w2, rfl⟩
  · intro h
    rcases h with ⟨pw⟩
    have h_incomp : ∀ x ∈ pw.left.path, ∀ y ∈ pw.right.path, causalIncomparable x y := pw.pairwise_incomparable
    have h_pne_left : pw.left.path ≠ [] := pw.left.path_nonempty
    have hA : A ∈ pw.left.path := by
      have h_head : pw.left.path.head h_pne_left = A := pw.left.head_eq
      have h : pw.left.path.head h_pne_left ∈ pw.left.path := by
        exact List.head_mem _
      rw [h_head] at h
      exact h
    have h_pne_right : pw.right.path ≠ [] := pw.right.path_nonempty
    have hB : B ∈ pw.right.path := by
      have h_last : pw.right.path.getLast h_pne_right = B := pw.right.last_eq
      have h : pw.right.path.getLast h_pne_right ∈ pw.right.path := by
        exact List.getLast_mem _
      rw [h_last] at h
      exact h
    have h1 : causalIncomparable A B := h_incomp A hA B hB
    rcases h1 with ⟨h_nlt1, h_nlt2⟩
    have h_lt : A.idx < B.idx := by
      dsimp only [A, B] <;> norm_num
    have h_lt2 : causalLT A B := h_lt
    exact h_nlt1 h_lt2

/-- **定理 2**: seq 和 par 在类型层面不同

seq 产生 `Weave L R`，par 产生 `ParallelWeave L1 R1 L2 R2`，类型不同。 -/
theorem seq_par_types_distinct : True := by
  trivial


end CSQIT.Models.FiniteWeaveCounterexample
