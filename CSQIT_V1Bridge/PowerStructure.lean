/-
================================================================================
CSQIT_V1Bridge — 因果层上的幂结构（G18）
模块: CSQIT_V1Bridge.PowerStructure
版本: v0.4.0（2026-11-07）
================================================================================

承接 `23_路径结论.md` §11（G12–G17）。上一轮已把因果-振幅层精确刻画为：
  Nonempty layer ↔ 无右作用元，且载体必无限（A，G6/G7）；
  AxiomC 强制 compose 交换（A，G14）；
  层无极大元、向上定向（A，G14）；
  见证模型给链、乘积模型给非链（A，G16/G17）。

本轮往下挖因果层的**事件结构**：在无右作用元模型（因果层承载的
必要条件）上，compose 构成半群；对任一事件 α，定义幂序列
α, α∘α, α∘α∘α, ...，证明：

  §1 幂定义（显式 compose 参数，避免 typeclass instance 问题）。

  §2 幂加法公式（G18 核心引理）：
      `power compose α n ∘ power compose α m = power compose α (n+m+1)`。
      只用 compose assoc，不需要 compose 交换。

  §3 无右作用元 ⇒ 幂两两不同（G18a，A 档）。

  §4 可达序下幂递增（G18b，A 档）。

  §5 振幅的幂性质（G18c，A 档）：
      amplitude α ≠ 1（amplitude 单射 + h_no_id α α）；
      amplitude 幂两两不同（amplitude 单射 + G18a 直接推出）。

纪律：零新增 axiom、零 sorry；只 import 既有模块；
      不修改 CSQIT_W1 / CSQIT_Enhanced / 既有 V1Bridge 文件。
================================================================================ -/

import CSQIT_W1.Foundation
import CSQIT_V1Bridge.OrderAndFixedPoint
import CSQIT_V1Bridge.CausalAmplitudeLayer

namespace CSQIT_V1Bridge

open CSQIT_W1.Foundation
open CSQIT_W1.CompilerAxioms

/-! ============================================================================
    §1. 幂定义（显式 compose 参数）
   ============================================================================ -/

/-- **半群幂**（显式 compose 参数，避免 typeclass instance）：
    `power compose α n` 从 α 开始，把 compose 迭代 n 次。
    具体：`power c α 0 = α`，`power c α (n+1) = c (power c α n) α`。
    所以 `power c α n` 共 compose α 恰好 `n+1` 次。 -/
noncomputable def power {C : Type*} (compose : C → C → C) (α : C) : ℕ → C
  | 0 => α
  | n + 1 => compose (power compose α n) α

/-- **幂的零次就是 α 本身**。 -/
lemma power_zero {C : Type*} {compose : C → C → C} (α : C) :
    power compose α 0 = α := rfl

/-- **幂的后继递归式**。 -/
lemma power_succ {C : Type*} {compose : C → C → C} (α : C) (n : ℕ) :
    power compose α (n + 1) = compose (power compose α n) α := rfl

/-! ============================================================================
    §2. 幂加法公式（只用结合律）
   ============================================================================ -/

/-- **幂加法公式**（G18 核心引理，W1）：
    给定 compose 结合律 `assoc`，
    `power compose α n ∘ power compose α m = power compose α (n + m + 1)`。

    这条只用 `assoc`，**不需要 compose 交换**——即使半群不交换也成立，
    因为所有操作元都是同一个 α，结合律足够。 -/
theorem power_add {C : Type*} {compose : C → C → C}
    (assoc : ∀ x y z : C, compose (compose x y) z = compose x (compose y z))
    (α : C) (n m : ℕ) :
    compose (power compose α n) (power compose α m) =
      power compose α (n + m + 1) := by
  induction m with
  | zero =>
    simp [power_zero, power_succ]
    <;> ring_nf
  | succ m ih =>
    calc
      compose (power compose α n) (power compose α (m + 1))
        = compose (power compose α n) (compose (power compose α m) α) := rfl
      _ = compose (compose (power compose α n) (power compose α m)) α := by
        exact (assoc (power compose α n) (power compose α m) α).symm
      _ = compose (power compose α (n + m + 1)) α := by rw [ih]
      _ = power compose α ((n + m + 1) + 1) := rfl
      _ = power compose α (n + (m + 1) + 1) := by ring_nf

/-! ============================================================================
    §3. 无右作用元 ⇒ 幂两两不同（G18a）
   ============================================================================ -/

/-- **G18a（W1，A 档）**：无右作用元 + compose assoc ⇒ α 的所有幂两两不同。

    反证核心：假设 n < m 且 power α n = power α m，令 d = m - n ≥ 1，
    由 power_add 有 power α m = compose (power α n) (power α (d-1))，
    与无右作用元条件矛盾。 -/
theorem no_right_id_implies_powers_ne {C : Type*} {compose : C → C → C}
    (assoc : ∀ x y z : C, compose (compose x y) z = compose x (compose y z))
    (h_no_id : ∀ x y : C, compose x y ≠ x) :
    ∀ (α : C) (n m : ℕ), n ≠ m → power compose α n ≠ power compose α m := by
  intro α n m hne
  have hlt_or_gt : n < m ∨ m < n := Nat.lt_or_gt_of_ne hne
  cases hlt_or_gt with
  | inl hlt =>
    by_contra h_contra
    have hd1 : ∃ k : ℕ, m - n = k + 1 := by
      refine ⟨(m - n) - 1, ?_⟩
      omega
    rcases hd1 with ⟨k, hk_eq⟩
    have hmd : m = n + (k + 1) := by omega
    rw [hmd] at h_contra
    -- h_contra: power α n = power α (n + (k + 1))
    have h : power compose α (n + (k + 1)) = power compose α n := h_contra.symm
    have h_comp : compose (power compose α n) (power compose α k) =
        power compose α (n + k + 1) := power_add assoc α n k
    have h_nkk1 : n + k + 1 = n + (k + 1) := by omega
    have h_comp' : compose (power compose α n) (power compose α k) =
        power compose α (n + (k + 1)) := by
      rw [h_nkk1] at h_comp; exact h_comp
    have h_eq : compose (power compose α n) (power compose α k) =
        power compose α n := h_comp'.trans h
    exact h_no_id (power compose α n) (power compose α k) h_eq
  | inr hgt =>
    by_contra h_contra
    have h_contra' : power compose α m = power compose α n := h_contra.symm
    have hd1 : ∃ k : ℕ, n - m = k + 1 := by
      refine ⟨(n - m) - 1, ?_⟩
      omega
    rcases hd1 with ⟨k, hk_eq⟩
    have hnd : n = m + (k + 1) := by omega
    rw [hnd] at h_contra'
    -- h_contra' 变成: power α m = power α (m + (k + 1))
    have h : power compose α (m + (k + 1)) = power compose α m := h_contra'.symm
    have h_comp : compose (power compose α m) (power compose α k) =
        power compose α (m + k + 1) := power_add assoc α m k
    have h_mkk1 : m + k + 1 = m + (k + 1) := by omega
    have h_comp' : compose (power compose α m) (power compose α k) =
        power compose α (m + (k + 1)) := by
      rw [h_mkk1] at h_comp; exact h_comp
    have h_eq : compose (power compose α m) (power compose α k) =
        power compose α m := h_comp'.trans h
    exact h_no_id (power compose α m) (power compose α k) h_eq

/-! ============================================================================
    §4. 可达序下幂递增（G18b）
   ============================================================================ -/

/-- **G18b（W1，A 档）**：无右作用元模型中，幂序列在可达序下严格递增。

    可达序构造（G1′）中 `β ≺ β' := ∃ γ, β' = β∘γ ∧ β' ≠ β`；
    取 γ = α 即可满足条件。
    本引理给出可达序构造的直接见证，不需要完整层结构。 -/
theorem power_reachable_succ {C : Type*} {compose : C → C → C}
    (assoc : ∀ x y z : C, compose (compose x y) z = compose x (compose y z))
    (h_no_id : ∀ x y : C, compose x y ≠ x)
    (α : C) (n : ℕ) :
    ∃ γ : C, power compose α (n + 1) = compose (power compose α n) γ ∧
              power compose α (n + 1) ≠ power compose α n := by
  refine ⟨α, ?_, ?_⟩
  · simp [power_succ]
  · have hne : n ≠ n + 1 := by omega
    have hne2 : power compose α n ≠ power compose α (n + 1) :=
      no_right_id_implies_powers_ne assoc h_no_id α n (n + 1) hne
    exact hne2.symm

/-! ============================================================================
    §5. 振幅的幂性质（G18c）
   ============================================================================ -/

/-- **G18c（W1，A 档）**：amplitude 的幂行为——
    `amplitude (power A.compose α n) = (amplitude α)^(n+1)`。
    只用 amplitude 的乘法性（comp_rule），不需要 compose 交换。 -/
theorem amplitude_pow_eq_pow_amplitude {M C : Type*} [A : AxiomA M C]
    [Cx : AxiomC M C] (α : C) (n : ℕ) :
    Cx.amplitude (power A.compose α n) = Cx.amplitude α ^ (n + 1) := by
  induction n with
  | zero =>
    simp [power_zero]
    <;> rfl
  | succ n ih =>
    have h : Cx.amplitude (power A.compose α (n + 1)) =
        Cx.amplitude (A.compose (power A.compose α n) α) := rfl
    rw [h]
    rw [Cx.comp_rule]
    rw [ih]
    <;> ring

/-- **amplitude α ≠ 1（W1，A 档，比 G14 更一般）**：
    只要 `h_no_id : ∀ x y, x∘y ≠ x`，就有 amplitude α ≠ 1。
    只用 amplitude_injective + compose assoc（compose assoc 来自 AxiomA）。 -/
theorem amplitude_ne_one_of_no_self_idem {M C : Type*} [A : AxiomA M C]
    [Cx : AxiomC M C]
    (h_no_id : ∀ x y : C, A.compose x y ≠ x) (α : C) :
    Cx.amplitude α ≠ 1 := by
  have h_self : A.compose α α ≠ α := h_no_id α α
  have h_amp : Cx.amplitude (A.compose α α) ≠ Cx.amplitude α :=
    Cx.amplitude_injective.ne h_self
  have h_eq : Cx.amplitude (A.compose α α) = Cx.amplitude α * Cx.amplitude α :=
    Cx.comp_rule α α
  rw [h_eq] at h_amp
  intro h_one
  rw [h_one] at h_amp
  <;> norm_num at h_amp

/-- **amplitude 在幂上两两不同（W1，A 档）**：
    直接用 amplitude_injective + G18a：幂两两不同 ⇒ 其 amplitude 两两不同。
    这条**独立于 amplitude α ≠ 1** 的显式假设——它只需要 amplitude 单射、
    compose assoc、无右作用元。

    这还隐含 amplitude α 不能是有限阶单位根：否则 amplitude α^d = amplitude α
    会给出 power α d = α（由 amplitude_injective），但 power α d ≠ α（G18a）。 -/
theorem amplitude_powers_ne {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (h_no_id : ∀ x y : C, A.compose x y ≠ x) :
    ∀ (α : C) (n m : ℕ), n ≠ m →
        Cx.amplitude (power A.compose α n) ≠ Cx.amplitude (power A.compose α m) := by
  intro α n m hne
  have h_assoc : ∀ x y z : C, A.compose (A.compose x y) z = A.compose x (A.compose y z) :=
    A.compose_assoc
  have h_powers_ne : power A.compose α n ≠ power A.compose α m :=
    no_right_id_implies_powers_ne h_assoc h_no_id α n m hne
  exact Cx.amplitude_injective.ne h_powers_ne

/-! ============================================================================
    §6. amplitude 无有限阶（G19）
   ============================================================================ -/

/-- **G19（W1，A 档）**：因果层模型上 amplitude α 不能是有限阶单位根。

    定义：z 有有限阶 d ≥ 1 当且仅当 z^d = 1。
    这会强制 amplitude (power α d) = amplitude (power α 0)（因为 z^(d+1) = z），
    与 amplitude_powers_ne（d ≠ 0 ⇒ amplitude (power α d) ≠ amplitude (power α 0)）
    矛盾。

    这条比 amplitude_powers_ne 弱——它只是 amplitude_powers_ne 的一个直接推论，
    但它的表述更贴近 V1 A5（测度刚性）中「同构因果集振幅相同」的最小翻译：
    至少 amplitude 值域不能是离散的有限集合。 -/
theorem amplitude_not_finite_order {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (h_no_id : ∀ x y : C, A.compose x y ≠ x)
    (α : C) (d : ℕ) (hd_pos : d ≥ 1)
    (h_z_d_eq_one : Cx.amplitude α ^ d = 1) :
    False := by
  have h_contra : Cx.amplitude (power A.compose α d) =
      Cx.amplitude (power A.compose α 0) := by
    have h_amp_d : Cx.amplitude (power A.compose α d) =
        Cx.amplitude α ^ (d + 1) := amplitude_pow_eq_pow_amplitude α d
    have h_amp_0 : Cx.amplitude (power A.compose α 0) =
        Cx.amplitude α ^ 1 := amplitude_pow_eq_pow_amplitude α 0
    rw [h_amp_d, h_amp_0]
    -- z^(d+1) = z · z^d = z · 1 = z
    rw [pow_succ]
    rw [h_z_d_eq_one]
    <;> ring
  have h_dne : d ≠ 0 := by omega
  have h_impossible := amplitude_powers_ne h_no_id α d 0 h_dne
  exact h_impossible h_contra

/-! ============================================================================
    汇总：G18 四档
   ============================================================================ -/
/-
  本轮新增三条核心结论（+ 三个辅助引理），全部零新增公设、零 sorry：

    G18a  无右作用元 + compose assoc ⇒ 幂两两不同       —— A 档
    G18b  可达序下幂严格递增                            —— A 档
    G18c  amplitude α ≠ 1 + 振幅幂两两不同（直接用单射）  —— A 档

  信息增益：
    G14 只证了「层中每个元素有后继」（存在量词）；
    G18 给出了后继的**可计算迭代**——幂序列是具体的、可量化的。
    这把因果层的「无极大元」从定性升级为定量：
    对任意 α，存在无穷严格递增链 α, α∘α, α∘α∘α, ... 在可达序下。
    且每个幂的振幅也两两不同。

    amplitude α ≠ 1 比 G14 的 layer_compose_self_ne 更底：
    后者需要完整层结构（compat + irrefl）；
    本引理只用 h_no_id α α（compose α α ≠ α）+ amplitude 单射。
================================================================================ -/

end CSQIT_V1Bridge
