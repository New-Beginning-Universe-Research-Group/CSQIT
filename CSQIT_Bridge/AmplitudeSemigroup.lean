/-
================================================================================
CSQIT_Bridge — 第二十六轮：G38/G39 的结构化收口（含诚实的重复性核查）
模块: CSQIT_Bridge.AmplitudeSemigroup
================================================================================

**核查结论（先说结论，避免夸大）**：G38/G39 的「结构定理」在既有轮次中
**已经成立**，本轮不再重复证明，只做三件事：

  (a) 汇总成单条可引用陈述 `amplitude_embedding_unitCircle`；
  (b) 把 G39 的「一正一反」合成单一充要条件
      `exists_compatible_order_iff_forall_pow_ne_one`；
  (c) 补上一条此前没有的**反例边界** `injective_amplitude_not_force_group`。

既有对应（不得重复计入本轮增量）：

| 本轮想证 | 既有定理 | 位置 |
|---|---|---|
| compose 交换 | `compose_comm_of_axiomC`（G14） | `CSQIT_V1Bridge/StructuralLimits.lean:110` |
| 左/右可消去 | `compose_left_cancel` / `compose_right_cancel`（G35） | `CSQIT_V1Bridge/AmplitudeStructure.lean:57,69` |
| 幂两两不同 | `no_right_id_implies_powers_ne`（G18a） | `CSQIT_V1Bridge/PowerStructure.lean:103` |
| 振幅幂公式 | `amplitude_pow_eq_pow_amplitude`（G18c） | `CSQIT_V1Bridge/PowerStructure.lean` |
| 振幅无有限阶 | `amplitude_not_finite_order`（G19） | `CSQIT_V1Bridge/PowerStructure.lean:243` |
| 幂等 ⇒ 振幅 1 | `amplitude_eq_one_of_idempotent`（G35b） | `CSQIT_V1Bridge/AmplitudeStructure.lean:83` |
| 有限载体必有右作用元 | `no_right_id_implies_infinite`（G7 对偶） | `CSQIT_V1Bridge/CausalLayerSharpening.lean:273` |

所以「因果层 ⇒ 载体无限」「因果层 ⇒ 振幅全为无限阶」「因果层 ⇒ 组合
交换且可消去」三条强结论**都不是本轮新得**，本轮只是把它们合并陈述。
本轮**唯一**的新数学是 §4 的反例：单射**不**迫使载体成为群。

纪律：零新增 axiom、零 sorry；不修改 CSQIT_W1 / CSQIT_Enhanced / 既有
V1Bridge 文件；新增仅本文件与 lakefile 一行 root。
================================================================================ -/

import CSQIT_V1Bridge.AmplitudeRigidity
import CSQIT_V1Bridge.PowerStructure
import CSQIT_V1Bridge.GeneralModelClassification

namespace CSQIT_Bridge

open CSQIT_W1.Foundation
open CSQIT_V1Bridge

/-! ============================================================================
  §1. 汇总陈述：C 是单位圆乘法的一个子半群像
   ============================================================================ -/

/-- **S1-a（A 档）**：振幅的模恒为 1。

    由 `norm_one`（`normSq = 1`）与 `normSq = ‖z‖²`、`‖z‖ ≥ 0` 推出。
    与 `CSQIT_LayerCuts.Cuts.amplitude_normSq_eq_one` 同源（那里是
    `normSq` 形式），此处给出 `‖·‖` 形式以便直接与单位圆对接。
    **证明什么**：振幅值域 ⊆ 单位圆。**不证明什么**：不涉及稠密性/可定义性。 -/
theorem amplitude_norm_eq_one {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (x : C) : ‖Cx.amplitude x‖ = 1 := by
  have h := Cx.norm_one x
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (Cx.amplitude x)]

/-- **S1-b（A 档，汇总）**：`C` 作为 magma 同构嵌入单位圆乘法。

    (1) `amp` 单射（G38 的 `amplitude_injective`）；
    (2) `amp` 保持复合（`comp_rule`）；
    (3) 像落在单位圆上（S1-a）。
    三条合起来即「`C` ≅ `S¹` 的某个子半群，`compose` = 单位圆乘法」。

    **证明什么**：载体的全部代数自由度**不超过**「`S¹` 的子半群」。
    **不证明什么**：
      · 不给子半群的分类（「闭子群 ⇒ 有限循环或全圆」需拓扑，本模块不引入）；
      · 不给出 o-minimal / 可定义性——那是对子半群类的外在限制，五字段+振幅
        结构对此**完全沉默**（例如 §4 的 ℕ 模型与圆群模型自由度相同）；
      · 不给出任何「维数上限」的陈述（`S¹` 的实维数 = 1 是 `S¹` 的属性，
        不是从公理推出的）。
    本条**不是新数学**：它是 G14 + G35 + G38 的合并陈述。 -/
theorem amplitude_embedding_unitCircle {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C] :
    Function.Injective Cx.amplitude ∧
      (∀ x y : C, Cx.amplitude (A.compose x y) = Cx.amplitude x * Cx.amplitude y) ∧
      (∀ x : C, ‖Cx.amplitude x‖ = 1) :=
  ⟨Cx.amplitude_injective, Cx.comp_rule, amplitude_norm_eq_one⟩

/-! ============================================================================
  §2. G39 的收支形态：因果层存在的充要条件
   ============================================================================ -/

/-- 迭代复合：`compPow A x n` 是 `x` 与自己复合 `n+1` 次（无单位元，从 1 次起算）。
    与 `CSQIT_V1Bridge.AmplitudeStructure.compPow` 参数顺序不同（那里以幂等元
    `e` 为基点），此处以任意元为起点，便于在无单位元假设下使用。 -/
def compPow {M C : Type*} (A : AxiomA M C) (x : C) : ℕ → C
  | 0 => x
  | n + 1 => A.compose x (compPow A x n)

/-- **S2-a（A 档）**：迭代复合的振幅是振幅的幂。与 G18c 同型。 -/
theorem amplitude_compPow {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (x : C) (n : ℕ) : Cx.amplitude (compPow A x n) = Cx.amplitude x ^ (n + 1) := by
  induction n with
  | zero => simp [compPow]
  | succ n ih =>
    show Cx.amplitude (A.compose x (compPow A x n)) = Cx.amplitude x ^ (n + 1 + 1)
    rw [Cx.comp_rule, ih, mul_comm (Cx.amplitude x) (Cx.amplitude x ^ (n + 1)), ← pow_succ]

/-- **S2-b（A 档，合并形态）**：`1 ∉ amp(C)` ⟺ `amp(C)` 全为无限阶元。

    (→) 即 G19（`amplitude_not_finite_order`）的等价改写：
        若 `amp y ^ n = 1`（`n > 0`），则 `amp (y^[n-1]) = 1`，把 `1` 拉回值域；
    (←) 取 `n = 1`，平凡。

    **证明什么**：因果层排除的正是**挠元素**——任何单位根（哪怕只出现一次）
    都会把 `1` 带回值域，从而彻底消灭因果层。
    **不证明什么**：不说明「哪些挠自由子半群可实现」；也不把「挠自由」
    翻译成任何物理断言。
    **诚实标注**：实质在 (→)，即 G19；(←) 平凡。本条价值在**合并成单一
    充要条件**，不构成新数学。 -/
theorem amplitude_ne_one_iff_forall_pow_ne_one {M C : Type*}
    [A : AxiomA M C] [Cx : AxiomC M C] :
    (∀ y : C, Cx.amplitude y ≠ 1) ↔
      (∀ (y : C) (n : ℕ), 0 < n → Cx.amplitude y ^ n ≠ 1) := by
  constructor
  · intro h y n hn hpow
    have hpos : n ≠ 0 := by omega
    have he : n - 1 + 1 = n := Nat.sub_one_add_one hpos
    exact h (compPow A y (n - 1)) (by rw [amplitude_compPow, he]; exact hpow)
  · intro h y hy
    exact h y 1 (by norm_num) (by simpa using hy)

/-- **S2-c（A 档，G39 的最终形态）**：因果层存在 ⟺ 全体振幅无限阶。

    合成 G39b（`∃ 相容序 ⟺ 1 ∉ amp(C)`）与 S2-b。这是本轮对 G39 的
    表述加强：把「1 不在值域」这个否定式条件，换成「值域挠自由」这个
    逐元素可检验的正向条件。 -/
theorem exists_compatible_order_iff_forall_pow_ne_one {M C : Type*}
    [A : AxiomA M C] [Cx : AxiomC M C] :
    (∃ r : C → C → Prop,
        (∀ x : C, ¬ r x x) ∧
        (∀ x y z : C, r x y → r y z → r x z) ∧
        (∀ α β : C, r α (A.compose α β))) ↔
      (∀ (y : C) (n : ℕ), 0 < n → Cx.amplitude y ^ n ≠ 1) := by
  rw [exists_compatible_order_iff_amplitude_ne_one (A := A) (Cx := Cx),
      amplitude_ne_one_iff_forall_pow_ne_one]

/-- **S2-d（A 档）**：因果层存在 ⇒ 振幅值域真包含于单位圆。

    值域含不了一个模为 1 的复数（取 `1` 本身），故像 ≠ `S¹`。
    这是 S1-b 「子半群」而非「整个圆群」的直接代价，也是与
    `no_right_id_implies_infinite` 相配的基数侧提示。 -/
theorem amplitude_range_proper_of_no_one {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (h : ∀ y : C, Cx.amplitude y ≠ 1) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ ∀ y : C, Cx.amplitude y ≠ z :=
  ⟨1, by norm_num, h⟩

/-! ============================================================================
  §3. 反例边界：单射不迫使载体成为群
   ============================================================================ -/

/-- **S3-a（A 档，新）**：存在 `AxiomC` 模型，振幅单射、复合可消去，
    但载体**不是群**——`ℕ` 上的加法模型。

    这精确界定 S1-b 的强度：`C` 只是「`S¹` 的子半群」，
    **不是**「子群」。任何「单射 ⇒ 群」的更强主张在此被证否。

    **证明什么**：`ℕ` 的 `1` 无加法逆元，而 `addAxiomCOfWitness` 的振幅单射。
    **不证明什么**：不排除另一些 `AxiomC` 模型确实是群（G33 的有限模型
    就是群），只说明「必然」为假；也不说明该模型有因果层（它的 `0` 使
    `1 ∈ amp`，故按 G39 **没有**因果层——「非群」与「有因果层」是两件事）。 -/
theorem injective_amplitude_not_force_group :
    ∃ Cx : @AxiomC ℕ ℕ addModel,
      Function.Injective Cx.amplitude ∧
        ¬ (∀ x : ℕ, ∃ y : ℕ, addModel.compose x y = 0) := by
  refine ⟨addAxiomCOfWitness, addAxiomCOfWitness.amplitude_injective, ?_⟩
  intro h
  obtain ⟨y, hy⟩ := h 1
  have h1 : 1 + y = 0 := hy
  omega

end CSQIT_Bridge
