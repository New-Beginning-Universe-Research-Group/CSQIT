/-
================================================================================
CSQIT_V1Bridge — 第二十二轮：振幅对组合的刚性（G38–G40）
模块: CSQIT_V1Bridge.AmplitudeRigidity
版本: v0.1.0（2026-11-08）
================================================================================

上一轮（G37）给出独立性图谱的一侧：`NeList` 模型上因果层存在、
振幅层不存在。本轮补上另一侧的结构性事实，并回答「因果性能否由
现有结构导出」的最后一块拼图：

  §1  G38：振幅决定组合。`AxiomC.amplitude` 是到单位圆的单射
      幺半同态，因此
        · 组合的相等 ⟺ 两个振幅标签的乘积相等（G38a）；
        · 给定标签乘积，组合元素被唯一钉死（G38b）；
        · 同一载体上两个 AxiomA/AxiomC 结构若振幅函数相同，则
          `compose` 完全相同（G38c）。
      这正是「C 就是单位圆的一个子半群（经 amplitude 搬运）」的
      精确陈述：组合层没有超出振幅标签的自由度。

  §2  G39：因果层的振幅判据。对任意 AxiomA + AxiomC 模型，
        x∘y = x  ⟺  amplitude y = 1          （G39a）
      于是 G34-pre 的「相容序存在 ⟺ 无右作用元」翻译为纯振幅条件：
        存在相容严格偏序  ⟺  1 不在 amplitude 的值域里   （G39b）
      推论：只要 AxiomC 存在，因果层（存在性与全部相容序）就是
      振幅场的函数——因果性不是独立于 e^{iS} 的另一层。

  §3  G40：独立性图谱补全（2×2）。新增两个模型条目：
        · 加法模型 `addModel`：无限载体、振幅层非空、**无**因果层
          （0 是右作用元 ⇒ amplitude 0 = 1）；
        · 左吸收模型 `leftAbsorbingAxiomA`：振幅层为空、**无**因果层。
      与 G33（Bool：振幅有/因果无）、G37（NeList：振幅无/因果有）、
      G24+G34（见证模型：两者皆有且因果序唯一）合起来，2×2 四格
      全部有具体见证。

判定档位：本文件全部定理均为 **A 档**（在既有 AxiomA/AxiomC 与
G34-pre 上直接可证，无新增公设；新增的只是陈述用的定理，不是
定义性公设）。

纪律：零新增 axiom、零 sorry；不修改 CSQIT_W1 / CSQIT_Enhanced，
也不修改既有 V1Bridge 文件；只新增本文件与 lakefile 一行 root。
依赖：CSQIT_V1Bridge.OrderUniqueness（G34-pre）、
      CSQIT_V1Bridge.GeneralModelClassification（add / 左吸收模型）、
      CSQIT_V1Bridge.LayerIndependence（NeList，仅文档引用）。
================================================================================ -/

import CSQIT_V1Bridge.OrderUniqueness
import CSQIT_V1Bridge.GeneralModelClassification
import CSQIT_V1Bridge.LayerIndependence

namespace CSQIT_V1Bridge

open CSQIT_W1.Foundation

/-! ============================================================================
    §1. G38：振幅决定组合
   ============================================================================ -/

/-- **G38a（W1，A 档）**：组合的相等 ⟺ 振幅标签乘积的相等。

    (→) 由 `comp_rule` 直接把两边换成振幅乘积；
    (←) 由 `amplitude_injective`。

    这条把 `compose : C → C → C` 的**全部信息**压到 `amplitude` 上：
    组合层不是独立于振幅层的自由度，而是单位圆乘法经 `amplitude`
    的搬运。 -/
theorem compose_eq_iff_amplitude_mul {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (x y x' y' : C) :
    A.compose x y = A.compose x' y' ↔
      Cx.amplitude x * Cx.amplitude y = Cx.amplitude x' * Cx.amplitude y' := by
  constructor
  · intro h
    rw [← Cx.comp_rule x y, ← Cx.comp_rule x' y', h]
  · intro h
    apply Cx.amplitude_injective
    rw [Cx.comp_rule x y, Cx.comp_rule x' y']
    exact h

/-- **G38b（W1，A 档）**：给定振幅标签乘积，组合元素被唯一钉死。

    若 `amp z = amp x * amp y`，则 `z = x∘y`。这是 G38a 的单点形式，
    后面 G38c 的证明直接用它。 -/
theorem compose_forced_by_amplitude {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (x y z : C) (hz : Cx.amplitude z = Cx.amplitude x * Cx.amplitude y) :
    z = A.compose x y := by
  apply Cx.amplitude_injective
  rw [hz, Cx.comp_rule]

/-- **G38c（W1，A 档）**：同一载体上两个 `AxiomA` + `AxiomC` 结构，
    若振幅函数相同，则 `compose` 完全相同。

    证明：`A₁.compose x y` 与 `A₂.compose x y` 都满足
    「振幅 = amp x · amp y」，由 G38b（对 `C₂` 使用）与单射即得相等。
    注意这**不需要**两个结构的 `input`/`output` 相同——被钉死的只是
    `compose`。对照 G20（同一 compose 可承载两个不同 amplitude），
    两个方向合起来说明：`compose` 与 `amplitude` 只在「振幅 → 组合」
    这一侧是冗余的，反方向不成立。 -/
theorem compose_eq_of_same_amplitude {M C : Type*}
    {A₁ A₂ : AxiomA M C} (C₁ : @AxiomC M C A₁) (C₂ : @AxiomC M C A₂)
    (h : C₁.amplitude = C₂.amplitude) (x y : C) :
    A₁.compose x y = A₂.compose x y := by
  have hgoal : C₂.amplitude (A₁.compose x y) = C₂.amplitude x * C₂.amplitude y := by
    rw [← h]
    exact C₁.comp_rule x y
  exact compose_forced_by_amplitude (A := A₂) (Cx := C₂) x y (A₁.compose x y) hgoal

/-- **G38d（W1，A 档）**：振幅相同 ⇒ 单步可达关系（G34 的 ρ）完全相同。

    因果层的「候选序空间」由 ρ 生成（G34：ρ 是最小相容序，且任何
    相容序都包含 ρ；非全序时 ρ 可被扩张）。因此本条说明：在 AxiomC
    模型上，因果层的**关系内容**已经由振幅场决定。 -/
theorem oneStepReach_eq_of_same_amplitude {M C : Type*}
    {A₁ A₂ : AxiomA M C} (C₁ : @AxiomC M C A₁) (C₂ : @AxiomC M C A₂)
    (h : C₁.amplitude = C₂.amplitude) :
    oneStepReach A₁ = oneStepReach A₂ := by
  have hcomp : A₁.compose = A₂.compose := by
    funext x y
    exact compose_eq_of_same_amplitude C₁ C₂ h x y
  funext x y
  show (∃ γ : C, y = A₁.compose x γ ∧ y ≠ x) =
       (∃ γ : C, y = A₂.compose x γ ∧ y ≠ x)
  rw [hcomp]

/-! ============================================================================
    §2. G39：因果层的振幅判据
   ============================================================================ -/

/-- **G39a（W1，A 档）**：`x∘y = x` ⟺ `amplitude y = 1`（对任意 x, y）。

    (→) `amp x = amp x * amp y`，由 `amp x ≠ 0` 消去；
    (←) `amp (x∘y) = amp x * 1 = amp x`，由单射。

    这条把 G34-pre 中「无右作用元」这个组合条件**逐点**翻译成振幅
    条件：右作用元恰是振幅为 1 的元素。它也统一解释了
    `phase_zero_implies_right_id`（相位 0 ⇔ 振幅 1）与 G35b
    （幂等元 ⇒ 振幅 1 ⇒ 单位元）。 -/
theorem compose_eq_left_iff_amplitude_eq_one {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (x y : C) : A.compose x y = x ↔ Cx.amplitude y = 1 := by
  constructor
  · intro hxy
    have hcomp : Cx.amplitude (A.compose x y) = Cx.amplitude x * Cx.amplitude y :=
      Cx.comp_rule x y
    rw [hxy] at hcomp
    have h' : Cx.amplitude x * Cx.amplitude y = Cx.amplitude x * 1 := by
      rw [mul_one]
      exact hcomp.symm
    exact mul_left_cancel₀ (amplitude_ne_zero x) h'
  · intro hy
    apply Cx.amplitude_injective
    rw [Cx.comp_rule, hy, mul_one]

/-- **G39b（W1，A 档）**：因果层存在的**纯振幅判据**。

    存在与 `compose` 相容的严格偏序 ⟺ `1` 不在 `amplitude` 的值域里。

    这是 G34-pre（纯 `AxiomA`）与 G39a 的直接合成：
      ∃ 相容序 ⟺ 无右作用元 ⟺ ∀ y, amp y ≠ 1。
    相比 G34-pre，这条把模型类条件（「无右作用元」）换成了**可直接
    检查的振幅条件**；相比 G6 的层级版本，它不需要
    `V1CausalAmplitudeLayer` 的包装。 -/
theorem exists_compatible_order_iff_amplitude_ne_one {M C : Type*}
    [A : AxiomA M C] [Cx : AxiomC M C] :
    (∃ r : C → C → Prop,
        (∀ x : C, ¬ r x x) ∧
        (∀ x y z : C, r x y → r y z → r x z) ∧
        (∀ α β : C, r α (A.compose α β))) ↔
    (∀ y : C, Cx.amplitude y ≠ 1) := by
  rw [exists_compatible_order_iff_no_right_id A]
  constructor
  · intro hno y hy
    exact hno y y ((compose_eq_left_iff_amplitude_eq_one y y).mpr hy)
  · intro hamp x y hxy
    exact hamp y ((compose_eq_left_iff_amplitude_eq_one x y).mp hxy)

/-- **G39c（W1，A 档）**：振幅相同 ⇒ 因果层存在性相同。

    两个共享振幅函数的模型，要么都承载相容严格偏序，要么都不承载。
    与 G38d 合起来：在 AxiomC 模型上，「因果层是否存在」与「因果层
    的候选关系」都不含超出振幅场的自由度。 -/
theorem compatible_order_exists_iff_of_same_amplitude {M C : Type*}
    {A₁ A₂ : AxiomA M C} (C₁ : @AxiomC M C A₁) (C₂ : @AxiomC M C A₂)
    (h : C₁.amplitude = C₂.amplitude) :
    (∃ r : C → C → Prop,
        (∀ x : C, ¬ r x x) ∧
        (∀ x y z : C, r x y → r y z → r x z) ∧
        (∀ α β : C, r α (A₁.compose α β))) ↔
    (∃ r : C → C → Prop,
        (∀ x : C, ¬ r x x) ∧
        (∀ x y z : C, r x y → r y z → r x z) ∧
        (∀ α β : C, r α (A₂.compose α β))) := by
  rw [exists_compatible_order_iff_amplitude_ne_one (A := A₁) (Cx := C₁),
      exists_compatible_order_iff_amplitude_ne_one (A := A₂) (Cx := C₂), h]

/-! ============================================================================
    §3. G40：独立性图谱补全（2×2 的四格见证）
   ============================================================================ -/

/-- **G40a（W1，A 档）**：加法模型无因果层。

    `addModel`（`compose a b = a + b`）上 `0` 是右作用元
    （`a + 0 = a`），故 G34-pre 的反面成立。注意这是**无限载体**上
    的「振幅有、因果无」实例（对照 G33 的有限 `Bool`）。 -/
theorem add_no_causal_layer :
    ¬ ∃ r : ℕ → ℕ → Prop,
        (∀ x : ℕ, ¬ r x x) ∧
        (∀ x y z : ℕ, r x y → r y z → r x z) ∧
        (∀ α β : ℕ, r α (addModel.compose α β)) := by
  intro h
  have hno : ∀ x y : ℕ, addModel.compose x y ≠ x :=
    (exists_compatible_order_iff_no_right_id addModel).mp h
  exact hno 0 0 rfl

/-- **G40b（W1，A 档）**：加法模型同时满足「振幅层非空」与「无因果层」。

    这条补全 G37 的另一侧：G37 是「因果有、振幅无」，本条是
    「振幅有、因果无」且载体无限，因此独立性不是有限性造成的假象。 -/
theorem add_amplitude_without_causality :
    Nonempty (@AxiomC ℕ ℕ addModel) ∧
    ¬ ∃ r : ℕ → ℕ → Prop,
        (∀ x : ℕ, ¬ r x x) ∧
        (∀ x y z : ℕ, r x y → r y z → r x z) ∧
        (∀ α β : ℕ, r α (addModel.compose α β)) :=
  ⟨⟨addAxiomCOfWitness⟩, add_no_causal_layer⟩

/-- **G40c（W1，A 档）**：左吸收模型「振幅层为空」且「无因果层」。

    `leftAbsorbingAxiomA`（`compose a b = a`）上：
    · `AxiomC` 空间为空（G26f）；
    · 无相容严格偏序（`compose a b = a` 对所有 b 成立，直接违反
      「无右作用元」）。
    这是 2×2 图谱的第四格（两者皆无）。 -/
theorem leftAbsorbing_no_amplitude_no_layer :
    ¬ Nonempty (@AxiomC ℕ ℕ leftAbsorbingAxiomA) ∧
    ¬ ∃ r : ℕ → ℕ → Prop,
        (∀ x : ℕ, ¬ r x x) ∧
        (∀ x y z : ℕ, r x y → r y z → r x z) ∧
        (∀ α β : ℕ, r α (leftAbsorbingAxiomA.compose α β)) := by
  refine ⟨no_axiomC_leftAbsorbing, ?_⟩
  intro h
  have hno : ∀ x y : ℕ, leftAbsorbingAxiomA.compose x y ≠ x :=
    (exists_compatible_order_iff_no_right_id leftAbsorbingAxiomA).mp h
  exact hno 0 0 rfl

end CSQIT_V1Bridge
