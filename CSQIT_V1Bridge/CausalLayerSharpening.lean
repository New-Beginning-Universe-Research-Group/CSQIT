/-
================================================================================
CSQIT_V1Bridge — 因果-振幅层的精确刻画（G6）+ 有限载体障碍（G7）
模块: CSQIT_V1Bridge.CausalLayerSharpening
版本: v0.3.0（2026-11-07）
================================================================================

上一轮（G5）给出了「无右单位元模型 ⇒ 层可构造」与「幂等元 ⇒ 层不存在」，
但这两条并不互补：前者只给充分条件，后者只给一类必要条件。本模块补上
精确刻画，并检验振幅分量在组合层中是否真的贡献了额外约束。

  §1 层存在性 ⟺ 无右作用元
      (a) 层 ⇒ ∀ x y, x∘y ≠ x        [compat + irrefl，直接]
      (b) ∀ x y, x∘y ≠ x ⇒ 层存在      [复用 G1 conditional_order + G5 相位引理]
      ⇒ Nonempty layer ↔ 无右作用元

  §2 振幅分量冗余
      任意满足 irrefl + trans + compat 的关系 r 都自动满足 phase_compat
      （因为 compat + irrefl 已经推出无右作用元，再用 G5 的相位引理）。
      于是：
        Nonempty layer ↔ ∃ r, (严格偏序 ∧ 与 compose 相容)
      即「因果-振幅层」比「相容严格偏序」没有多出任何约束；
      振幅场在组合层中不提供额外结构。

判定：以上均为 A 档（可证），且只依赖既有 W1 定义与 G1/G5 定理。

  §3 有限载体不可能承载层（G7）
      有限半群必含幂等元（只用 compose_assoc 重建）；
      幂等元 ⇒ 层不存在（G5）。
      ⇒ 任何 Fintype 载体都不承载层，且「无右作用元」强制载体无限。
      这把 G1 条件构造的适用域从「某个模型类」收窄为
      「无限 + 无右作用元」。

纪律：零新增 axiom、零 sorry；不改既有文件；不 import 除既有 V1Bridge
      模块之外的任何项目文件。

依赖：CSQIT_V1Bridge.CausalAmplitudeLayer（→ OrderAndFixedPoint,
      OrderAndAction, CompilerAxioms, Foundation）。
================================================================================ -/

import CSQIT_V1Bridge.CausalAmplitudeLayer

namespace CSQIT_V1Bridge

open CSQIT_W1.CompilerAxioms
open CSQIT_W1.Foundation

/-! ## §1 层存在性 ⟺ 无右作用元 -/

/-- **G6(a)（W1，A 档）**：任何因果-振幅层都强制 `compose` 没有右作用元。

    证明：`compat α β` 给出 `α ≺ α∘β`；若 `α∘β = α`，则 `α ≺ α`，
    与 `irrefl` 矛盾。注意这里没有用到 `phase_compat`。 -/
theorem layer_implies_no_right_id {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (layer : V1CausalAmplitudeLayer (M := M) (C := C)) :
    ∀ x y : C, A.compose x y ≠ x := by
  intro x y hxy
  have hc : layer.causalOrder x (A.compose x y) := layer.compat x y
  rw [hxy] at hc
  exact layer.irrefl x hc

/-- **G6(b)（W1，A 档）**：层存在性恰好等价于无右作用元。

    (→) 是 G6(a)；(←) 是 G5 的 `layer_constructible_on_no_right_id`。
    这把上一轮「充分条件 / 一类必要条件」两条结果闭合为精确刻画：
    幂等元障碍只是无右作用元障碍的特例（`α∘α = α`，取 `y = α`）。 -/
theorem nonempty_layer_iff_no_right_id {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C] :
    Nonempty (V1CausalAmplitudeLayer (M := M) (C := C)) ↔
      (∀ x y : C, A.compose x y ≠ x) := by
  constructor
  · rintro ⟨layer⟩
    exact layer_implies_no_right_id layer
  · intro h
    exact layer_constructible_on_no_right_id (M := M) (C := C) h

/-! ## §2 振幅分量在组合层中冗余 -/

/-- **G6(c)（W1，A 档）**：`phase_compat` 不是独立约束，而是
    `irrefl + compat` 的推论。

    给定任意关系 `r`，只要它反自反并与 `compose` 相容，就已经强制
    `∀ x y, x∘y ≠ x`；再由 G5 的 `no_right_id_implies_all_phases_nonzero`
    得到所有相位非零。因此振幅场对「因果-振幅层」没有额外贡献。 -/
theorem phase_compat_of_causal_fields {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    {r : C → C → Prop}
    (hirrefl : ∀ x : C, ¬ r x x)
    (hcompat : ∀ α β : C, r α (A.compose α β)) :
    ∀ α β γ : C, β = A.compose α γ → r α β →
      (@actionPhase M C A Cx γ) ≠ (0 : Real.Angle) := by
  have h_no_id : ∀ x y : C, A.compose x y ≠ x := by
    intro x y hxy
    have hc : r x (A.compose x y) := hcompat x y
    rw [hxy] at hc
    exact hirrefl x hc
  intro α β γ _ _
  exact no_right_id_implies_all_phases_nonzero (M := M) (C := C) h_no_id γ

/-- **G6(d)（W1，A 档）**：组合层与「相容严格偏序」一一对应。

    因此上一轮定义的 `V1CausalAmplitudeLayer` 中，只有 `causalOrder`
    及其序公理是实质性内容；`phase_compat` 自动成立，振幅场只是
    被检查而不被约束。用四档表述：V1 的「因果 + 振幅」独立层在 v23 中
    退化为纯因果层（A 档）。 -/
theorem nonempty_layer_iff_exists_compatible_order {M C : Type*}
    [A : AxiomA M C] [Cx : AxiomC M C] :
    Nonempty (V1CausalAmplitudeLayer (M := M) (C := C)) ↔
      ∃ r : C → C → Prop,
        (∀ x : C, ¬ r x x) ∧
        (∀ x y z : C, r x y → r y z → r x z) ∧
        (∀ α β : C, r α (A.compose α β)) := by
  constructor
  · rintro ⟨layer⟩
    exact ⟨layer.causalOrder, layer.irrefl, layer.trans, layer.compat⟩
  · rintro ⟨r, hirrefl, htrans, hcompat⟩
    exact ⟨{
      causalOrder := r
      irrefl := hirrefl
      trans := htrans
      compat := hcompat
      phase_compat := phase_compat_of_causal_fields hirrefl hcompat }⟩

/-! ## §3 有限载体不可能承载层（G7）

    组合层存在 ⟺ 无右作用元（G6）。下一问：哪些载体能承载它？
    经典有限半群事实：有限半群必含幂等元。若把这个事实在 v23 的
    `compose` 上重建，就得到：任何有限 `C` 都含幂等元，从而
    `no_layer_when_idempotent` 直接排除层。

    推论：无右作用元模型的载体必为无限；上一轮 G5 的构造只在无限
    载体上可能。这不依赖 AxiomC，只用 `compose_assoc`。 -/

namespace FiniteSemigroup

variable {C : Type*}

/-- 左结合幂链：`pw f a n` 表示 `n+1` 份 `a` 的左结合乘积。
    只用 `f` 与 `n`，不需要单位元（载体不是幺半群）。 -/
def pw (f : C → C → C) (a : C) : ℕ → C
  | 0 => a
  | n + 1 => f (pw f a n) a

lemma pw_succ (f : C → C → C) (a : C) (n : ℕ) :
    pw f a (n + 1) = f (pw f a n) a := rfl

/-- 幂链的乘法分解：`pw (m+n+1) = pw m ∘ pw n`。 -/
lemma pw_add (f : C → C → C)
    (hassoc : ∀ a b c : C, f (f a b) c = f a (f b c))
    (a : C) (m : ℕ) :
    ∀ n : ℕ, pw f a (m + n + 1) = f (pw f a m) (pw f a n) := by
  intro n
  induction n with
  | zero => simp [pw]
  | succ n ih =>
      calc
        pw f a (m + (n + 1) + 1) = pw f a ((m + n + 1) + 1) := by
          congr 1
        _ = f (pw f a (m + n + 1)) a := pw_succ f a (m + n + 1)
        _ = f (f (pw f a m) (pw f a n)) a := by rw [ih]
        _ = f (pw f a m) (f (pw f a n) a) := hassoc _ _ _
        _ = f (pw f a m) (pw f a (n + 1)) := by rw [pw_succ f a n]

/-- 一旦幂链出现一次重复 `pw i = pw (i+d)`，该差值 `d` 会永久保持。
    注意：本条不需要结合律，只用 `pw_succ`。 -/
lemma pw_period (f : C → C → C)
    (a : C) (i d : ℕ) (hper : pw f a i = pw f a (i + d)) :
    ∀ t : ℕ, pw f a (i + t) = pw f a (i + t + d) := by
  intro t
  induction t with
  | zero => simpa using hper
  | succ t ih =>
      calc
        pw f a (i + (t + 1)) = pw f a ((i + t) + 1) := by
          congr 1
        _ = f (pw f a (i + t)) a := pw_succ f a (i + t)
        _ = f (pw f a (i + t + d)) a := by rw [ih]
        _ = pw f a ((i + t + d) + 1) := by rw [pw_succ f a (i + t + d)]
        _ = pw f a (i + (t + 1) + d) := by
          congr 1
          omega

/-- 周期 `d` 可迭代 `k` 次。不需要结合律。 -/
lemma pw_shift (f : C → C → C)
    (a : C) (i d : ℕ) (hper : pw f a i = pw f a (i + d)) :
    ∀ k t : ℕ, pw f a (i + t) = pw f a (i + t + k * d) := by
  intro k
  induction k with
  | zero =>
      intro t
      simp
  | succ k ih =>
      intro t
      have hp := pw_period f a i d hper (t + k * d)
      calc
        pw f a (i + t) = pw f a (i + t + k * d) := ih t
        _ = pw f a (i + (t + k * d)) := by
          congr 1
          omega
        _ = pw f a (i + (t + k * d) + d) := hp
        _ = pw f a (i + t + (k + 1) * d) := by
          rw [Nat.succ_mul]
          congr 1
          omega

/-- 幂链中出现一次重复即可抽出幂等元。 -/
lemma exists_idempotent_of_period (f : C → C → C)
    (hassoc : ∀ a b c : C, f (f a b) c = f a (f b c))
    {a : C} {i j : ℕ} (hij : i < j) (hEq : pw f a i = pw f a j) :
    ∃ e : C, f e e = e := by
  let d : ℕ := j - i
  have hd : 0 < d := by omega
  have hdj : i + d = j := by omega
  have hper : pw f a i = pw f a (i + d) := by
    rw [hdj]
    exact hEq
  -- 取 M = (i+2)·d，N = M-1；则 N+1 是 d 的倍数，且 N ≥ i。
  let M : ℕ := (i + 2) * d
  have hM_ge : i + 2 ≤ M := Nat.le_mul_of_pos_right (i + 2) hd
  let N : ℕ := M - 1
  have hM_one : 1 ≤ M := by omega
  have hN1 : N + 1 = M := Nat.sub_add_cancel hM_one
  have hi_lt_M : i < M := by omega
  have hN_ge_i : i ≤ N := Nat.le_pred_of_lt hi_lt_M
  let t : ℕ := N - i
  have ht : i + t = N := Nat.add_sub_of_le hN_ge_i
  have hshift : pw f a (i + t) = pw f a (i + t + (i + 2) * d) :=
    pw_shift f a i d hper (i + 2) t
  have hidx : i + t + (i + 2) * d = 2 * N + 1 := by
    have hMt : (i + 2) * d = M := rfl
    rw [hMt, ht, ← hN1]
    omega
  have hN_eq : pw f a N = pw f a (2 * N + 1) := by
    rw [hidx, ht] at hshift
    exact hshift
  refine ⟨pw f a N, ?_⟩
  have hpw := pw_add f hassoc a N N
  have hidx2 : N + N + 1 = 2 * N + 1 := by omega
  rw [hidx2] at hpw
  exact hpw.symm.trans hN_eq.symm

/-- **G7(a)（W1，A 档）**：有限非空半群必含幂等元。
    只用结合律，不需要单位元、交换律或任何 v23 公理。 -/
theorem exists_idempotent_of_fintype [Fintype C] [Nonempty C]
    (f : C → C → C)
    (hassoc : ∀ a b c : C, f (f a b) c = f a (f b c)) :
    ∃ e : C, f e e = e := by
  let a : C := Classical.choice (inferInstance : Nonempty C)
  obtain ⟨i, j, hij, hEq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n => pw f a n)
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · exact exists_idempotent_of_period f hassoc hlt hEq
  · exact exists_idempotent_of_period f hassoc hgt hEq.symm

end FiniteSemigroup

/-- **G7(b)（W1，A 档）**：任何有限载体模型都不承载因果-振幅层。

    `exists_idempotent_of_fintype` 给出幂等元 `e`，再由 G5 的
    `no_layer_when_idempotent` 排除层。于是层存在要求在
    `AxiomA + AxiomC` 下载体必须无限。 -/
theorem no_layer_of_fintype {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    [Fintype C] [Nonempty C] :
    V1CausalAmplitudeLayer (M := M) (C := C) → False := by
  intro layer
  obtain ⟨e, he⟩ :=
    FiniteSemigroup.exists_idempotent_of_fintype (f := A.compose) A.compose_assoc
  exact no_layer_when_idempotent (M := M) (C := C) ⟨e, he⟩ layer

/-- **G7(c)（W1，A 档）**：无右作用元强制载体无限。

    不依赖 AxiomC；只用 `compose_assoc` 与有限性。
    这与 G1 的条件构造互补：条件序只能存在于无限载体上，
    因此它在 v23 的有限模型（如 `Unit`、`Fin 7`）上恒为空。 -/
theorem no_right_id_implies_infinite {M C : Type*} [A : AxiomA M C]
    [Fintype C] [Nonempty C] :
    ¬ (∀ x y : C, A.compose x y ≠ x) := by
  intro h
  obtain ⟨e, he⟩ :=
    FiniteSemigroup.exists_idempotent_of_fintype (f := A.compose) A.compose_assoc
  exact h e e he

end CSQIT_V1Bridge
