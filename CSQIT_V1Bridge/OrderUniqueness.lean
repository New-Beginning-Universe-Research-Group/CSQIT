/-
================================================================================
CSQIT_V1Bridge — 第十九轮：因果序唯一性二分的一般化（G34）
模块: CSQIT_V1Bridge.OrderUniqueness
版本: v0.1.0（2026-11-08）
================================================================================

上一轮（G29–G33）给出了因果序唯一性的二分，但只在两个典范模型上：
见证模型（可达序全序 ⇒ 唯一，G29）与乘积模型（非全序 + 构造性第二序，
G30）。§18.6 登记的缺口是：**「非全序 ⇒ 必不唯一」的一般反命题未证**。
本模块闭合该缺口，把二分推广到**任意** `AxiomA` 模型。

核心观察：在无右作用元模型上，单步可达关系
    ρ x y := ∃ γ, y = x∘γ ∧ y ≠ x
本身就是一个相容严格偏序。传递性的机制：ρ x y 与 ρ y z 给出
z = (x∘γ)∘δ = x∘(γ∘δ)（结合律把回头路压成单步），而 z ≠ x 恰由
无右作用元排除。因此 ρ 是所有相容序中的**最小元**（G34b），
不需要 Mathlib 的传递闭包。

  §1  ρ 的一般性质（G34a）：反自反、传递（需无右作用元）、相容；
      以及关系级「相容序存在 ↔ 无右作用元」（G34-pre，纯 AxiomA，
      强于 G6 的层级版本——后者需要 AxiomC）。
  §2  最小性（G34b）：ρ ⊆ 任何相容序。
  §3  全序 ⇒ 唯一（G34c）：任何相容序都等于 ρ（G29a 的关系级封装）。
  §4  非全序 ⇒ 不唯一（G34d，新）：给定一对 ρ-不可比点 x₀, y₀，
      在 ρ 上「只加一条边 x₀ ≺ y₀ 并闭包」得到第二个相容序
      extReach ≠ ρ。这闭合 §18.6 登记的缺口。
  §5  二分主定理（G34e/G34f）：在无右作用元模型上，
        相容序唯一  ↔  ρ 全序
      关系级（G34e，纯 AxiomA）与层级（G34f，V1CausalAmplitudeLayer）。
  §6  典范模型实例化（G34g）：见证模型唯一侧、乘积模型不唯一侧。

结构性结论：因果层的自由度**恰且仅**由「时空中存在 ρ-不可比事件」
产生——这在所有模型上成立，不再限于两个典范模型。G29b/G29d/G30c
都成为 G34e/G34f 的实例。

判定档位：本文件所有定理均为 A 档（可证，无新增公设、无新增定义性
结构——`oneStepReach`/`extReach` 是既有 G9/G30 构造的一般化包装）。
纪律：零新增 axiom、零 sorry；不修改 CSQIT_W1 / CSQIT_Enhanced /
      既有 V1Bridge 文件；只新增本文件与 lakefile 一行 root。
依赖：CSQIT_V1Bridge.OrderRigidity（→ CausalSetWitness, NonTotalModel,
      GaugeAndEndo → LayerWitness → CausalLayerSharpening →
      CausalAmplitudeLayer → OrderAndFixedPoint）。
================================================================================ -/

import CSQIT_V1Bridge.OrderRigidity

namespace CSQIT_V1Bridge

open CSQIT_W1.CompilerAxioms
open CSQIT_W1.Foundation

/-! ============================================================================
    §1. G34a：单步可达关系 ρ 的一般性质（纯 AxiomA）
   ============================================================================ -/

/-- 任意 `AxiomA` 模型上的单步可达关系：`ρ x y` 当且仅当存在 γ 使
    `y = x∘γ` 且 `y ≠ x`。这是 G9/G29 中「可达序」的一般化定义。 -/
@[reducible]
def oneStepReach {M C : Type*} (A : AxiomA M C) (x y : C) : Prop :=
  ∃ γ : C, y = A.compose x γ ∧ y ≠ x

/-- **G34a-1（W1，A 档）**：ρ 反自反。不需要任何模型假设
    （定义中的 `y ≠ x` 直接排除 `x = x`）。 -/
theorem oneStepReach_irrefl {M C : Type*} (A : AxiomA M C) (x : C) :
    ¬ oneStepReach A x x := by
  rintro ⟨γ, _, hne⟩
  exact hne rfl

/-- **G34a-2（W1，A 档）**：无右作用元 ⇒ ρ 传递。

    机制：`y = x∘γ`、`z = y∘δ` 给出 `z = (x∘γ)∘δ = x∘(γ∘δ)`（结合律）；
    若 `z = x` 则 `x∘(γ∘δ) = x` 违反无右作用元。结合律把回头路压成
    单步，无右作用元再把单步回头路排除——两步合起来消灭一切环。 -/
theorem oneStepReach_trans {M C : Type*} (A : AxiomA M C)
    (hno : ∀ x y : C, A.compose x y ≠ x) {x y z : C}
    (hxy : oneStepReach A x y) (hyz : oneStepReach A y z) :
    oneStepReach A x z := by
  obtain ⟨γ, hγ, -⟩ := hxy
  obtain ⟨δ, hδ, -⟩ := hyz
  have hz : z = A.compose x (A.compose γ δ) := by
    rw [hδ, hγ, A.compose_assoc]
  refine ⟨A.compose γ δ, hz, ?_⟩
  intro hzx
  exact hno x (A.compose γ δ) (hz.symm.trans hzx)

/-- **G34a-3（W1，A 档）**：无右作用元 ⇒ ρ 与 compose 相容。 -/
theorem oneStepReach_compat {M C : Type*} (A : AxiomA M C)
    (hno : ∀ x y : C, A.compose x y ≠ x) (α β : C) :
    oneStepReach A α (A.compose α β) :=
  ⟨β, rfl, hno α β⟩

/-- **G34a（W1，A 档）**：无右作用元 ⇒ ρ 是一个相容严格偏序（三性质合取）。 -/
theorem oneStepReach_compatible {M C : Type*} (A : AxiomA M C)
    (hno : ∀ x y : C, A.compose x y ≠ x) :
    (∀ x : C, ¬ oneStepReach A x x) ∧
    (∀ x y z : C, oneStepReach A x y → oneStepReach A y z → oneStepReach A x z) ∧
    (∀ α β : C, oneStepReach A α (A.compose α β)) :=
  ⟨oneStepReach_irrefl A, fun x y z => oneStepReach_trans A hno,
    oneStepReach_compat A hno⟩

/-- **G34-pre（W1，A 档）**：关系级的层存在性刻画——
    存在与 compose 相容的严格偏序 **⟺** 无右作用元。

    (→) 同 G6(a)：compat + irrefl 直接给出。
    (←) 取 r := ρ（G34a）。

    这强于 G6 的层级版本（`nonempty_layer_iff_no_right_id`）：
    后者需要 `AxiomC` 实例，本条是纯 `AxiomA` 的。 -/
theorem exists_compatible_order_iff_no_right_id {M C : Type*} (A : AxiomA M C) :
    (∃ r : C → C → Prop,
        (∀ x : C, ¬ r x x) ∧
        (∀ x y z : C, r x y → r y z → r x z) ∧
        (∀ α β : C, r α (A.compose α β))) ↔
    (∀ x y : C, A.compose x y ≠ x) := by
  constructor
  · rintro ⟨r, hirrefl, -, hcompat⟩ x y hxy
    have hc : r x (A.compose x y) := hcompat x y
    rw [hxy] at hc
    exact hirrefl x hc
  · intro hno
    exact ⟨oneStepReach A, fun x => oneStepReach_irrefl A x,
      fun x y z => oneStepReach_trans A hno, oneStepReach_compat A hno⟩

/-! ============================================================================
    §2. G34b：ρ 是最小相容序
   ============================================================================ -/

/-- **G34b（W1，A 档）**：ρ 包含于任何与 compose 相容的关系。

    `ρ x y` 给出 `y = x∘γ`；compat 给出 `r x (x∘γ)`；重写即得。
    注意不需要 irrefl/trans，也不需要无右作用元。
    这是 G9（`reachable_subset_of_compatible`）的一般化重述。 -/
theorem oneStepReach_subset_of_compatible {M C : Type*} (A : AxiomA M C)
    {r : C → C → Prop} (hcompat : ∀ α β : C, r α (A.compose α β))
    {x y : C} (h : oneStepReach A x y) : r x y := by
  obtain ⟨γ, hγ, -⟩ := h
  have hc := hcompat x γ
  rwa [← hγ] at hc

/-! ============================================================================
    §3. G34c：ρ 全序 ⇒ 相容序唯一
   ============================================================================ -/

/-- **G34c（W1，A 档）**：若 ρ 全序（每对不同点至少一个方向可达），
    则任何两个相容严格偏序逐点等价——它们都等于 ρ。

    机制（G29a 的封装）：`r x y` 与 `x ≠ y` 排除 `ρ y x`（否则传递性
    给出 `r x x`），全序性遂给出 `ρ x y`；反向由 G34b。 -/
theorem compatible_orders_agree_of_reach_total {M C : Type*} (A : AxiomA M C)
    (htotal : ∀ x y : C, x ≠ y → oneStepReach A x y ∨ oneStepReach A y x)
    (r₁ r₂ : C → C → Prop)
    (hi₁ : ∀ x : C, ¬ r₁ x x) (ht₁ : ∀ x y z : C, r₁ x y → r₁ y z → r₁ x z)
    (hc₁ : ∀ α β : C, r₁ α (A.compose α β))
    (hi₂ : ∀ x : C, ¬ r₂ x x) (ht₂ : ∀ x y z : C, r₂ x y → r₂ y z → r₂ x z)
    (hc₂ : ∀ α β : C, r₂ α (A.compose α β)) :
    ∀ x y : C, r₁ x y ↔ r₂ x y := by
  intro x y
  rw [eq_reach_of_reach_total (A := A) (r := r₁) hi₁ ht₁ hc₁ htotal x y,
      eq_reach_of_reach_total (A := A) (r := r₂) hi₂ ht₂ hc₂ htotal x y]

/-! ============================================================================
    §4. G34d：ρ 非全序 ⇒ 相容序不唯一（闭合 §18.6 缺口）
   ============================================================================ -/

/-- **第二相容序的构造**：在 ρ 上「只加一条边 `x₀ ≺ y₀`」并按传递性
    闭包。显式形式：
      extReach u v := ρ u v ∨ ((ρ u x₀ ∨ u = x₀) ∧ (v = y₀ ∨ ρ y₀ v))
    即：原本可达的照旧；新边允许「u 可达 x₀（或就是 x₀）」跳到
    「v = y₀ 或 v 可达自 y₀」。

    合法性条件：x₀ ≠ y₀ 且 ρ y₀ x₀ 不成立（否则新边造环）。
    ρ x₀ y₀ 不成立只用于证明 extReach ≠ ρ。 -/
@[reducible]
def extReach {M C : Type*} (A : AxiomA M C) (x₀ y₀ u v : C) : Prop :=
  oneStepReach A u v ∨
    ((oneStepReach A u x₀ ∨ u = x₀) ∧ (v = y₀ ∨ oneStepReach A y₀ v))

/-- **G34d-1（W1，A 档）**：extReach 反自反。
    四种情形分别被 `x₀ ≠ y₀`、`¬ρ y₀ x₀` 与 ρ 的反自反排除。 -/
theorem extReach_irrefl {M C : Type*} (A : AxiomA M C)
    (hno : ∀ x y : C, A.compose x y ≠ x) {x₀ y₀ : C} (hne : x₀ ≠ y₀)
    (h₂ : ¬ oneStepReach A y₀ x₀) (u : C) : ¬ extReach A x₀ y₀ u u := by
  rintro (hur | ⟨hpu, hqu⟩)
  · exact oneStepReach_irrefl A u hur
  · rcases hpu with hux | hux
    · rcases hqu with huy | hyu
      · exact h₂ (huy ▸ hux)
      · exact h₂ (oneStepReach_trans A hno hyu hux)
    · rcases hqu with huy | hyu
      · exact hne (hux.symm.trans huy)
      · exact h₂ (hux ▸ hyu)

/-- **G34d-2（W1，A 档）**：extReach 传递。
    第二、三象限直接由 ρ 的传递；双新边象限被 `¬ρ y₀ x₀` 与
    `x₀ ≠ y₀` 逐一排除（穿过新边绕回 y₀ ⇔ ρ y₀ x₀）。 -/
theorem extReach_trans {M C : Type*} (A : AxiomA M C)
    (hno : ∀ x y : C, A.compose x y ≠ x) {x₀ y₀ : C} (hne : x₀ ≠ y₀)
    (h₂ : ¬ oneStepReach A y₀ x₀) {u v w : C}
    (huv : extReach A x₀ y₀ u v) (hvw : extReach A x₀ y₀ v w) :
    extReach A x₀ y₀ u w := by
  rcases huv with hur | ⟨hpu, hqv⟩
  · rcases hvw with hvr | ⟨hpv, hqw⟩
    · exact Or.inl (oneStepReach_trans A hno hur hvr)
    · rcases hpv with hvx | hvx
      · exact Or.inr ⟨Or.inl (oneStepReach_trans A hno hur hvx), hqw⟩
      · exact Or.inr ⟨Or.inl (hvx ▸ hur), hqw⟩
  · rcases hvw with hvr | ⟨hpv, hqw⟩
    · rcases hqv with hvy | hyv
      · exact Or.inr ⟨hpu, Or.inr (show oneStepReach A y₀ w by rw [← hvy]; exact hvr)⟩
      · exact Or.inr ⟨hpu, Or.inr (oneStepReach_trans A hno hyv hvr)⟩
    · exfalso
      rcases hpv with hvx | hvx
      · rcases hqv with hvy | hyv
        · exact h₂ (hvy ▸ hvx)
        · exact h₂ (oneStepReach_trans A hno hyv hvx)
      · rcases hqv with hvy | hyv
        · exact hne (hvx.symm.trans hvy)
        · exact h₂ (hvx ▸ hyv)

/-- **G34d-3（W1，A 档）**：extReach 与 compose 相容（新边不产生新 obligation）。 -/
theorem extReach_compat {M C : Type*} (A : AxiomA M C)
    (hno : ∀ x y : C, A.compose x y ≠ x) {x₀ y₀ : C} (α β : C) :
    extReach A x₀ y₀ α (A.compose α β) :=
  Or.inl ⟨β, rfl, hno α β⟩

/-- **G34d-4（W1，A 档）**：新边确实被加进：`extReach x₀ y₀`。 -/
theorem extReach_at_pair {M C : Type*} (A : AxiomA M C) (x₀ y₀ : C) :
    extReach A x₀ y₀ x₀ y₀ :=
  Or.inr ⟨Or.inr rfl, Or.inl rfl⟩

/-- **G34d（W1，A 档，本模块主构造）**：若 ρ 非全序——存在一对互不可达
    的不同点 x₀, y₀——则存在**两个不同的**相容严格偏序（ρ 与 extReach）。

    这闭合 §18.6 登记的缺口「G30 二分的一般反命题（非全序 ⇒ 必不唯一）
    未证」：该反命题现在对**任意** AxiomA 模型成立，不再依赖具体的
    乘积模型构造。 -/
theorem compatible_order_not_unique_of_reach_not_total {M C : Type*} (A : AxiomA M C)
    (hno : ∀ x y : C, A.compose x y ≠ x) {x₀ y₀ : C} (hne : x₀ ≠ y₀)
    (h₁ : ¬ oneStepReach A x₀ y₀) (h₂ : ¬ oneStepReach A y₀ x₀) :
    ∃ (r₁ r₂ : C → C → Prop),
      (∀ x : C, ¬ r₁ x x) ∧ (∀ x y z : C, r₁ x y → r₁ y z → r₁ x z) ∧
      (∀ α β : C, r₁ α (A.compose α β)) ∧
      (∀ x : C, ¬ r₂ x x) ∧ (∀ x y z : C, r₂ x y → r₂ y z → r₂ x z) ∧
      (∀ α β : C, r₂ α (A.compose α β)) ∧
      r₂ x₀ y₀ ∧ ¬ r₁ x₀ y₀ :=
  ⟨oneStepReach A, extReach A x₀ y₀,
    oneStepReach_irrefl A, fun x y z => oneStepReach_trans A hno, oneStepReach_compat A hno,
    extReach_irrefl A hno hne h₂, fun x y z => extReach_trans A hno hne h₂,
    extReach_compat A hno,
    extReach_at_pair A x₀ y₀, h₁⟩

/-! ============================================================================
    §5. G34e/G34f：唯一性二分主定理
   ============================================================================ -/

/-- **G34e（W1，A 档，主定理·关系级）**：在无右作用元模型上，
    相容严格偏序唯一 **⟺** 可达序 ρ 全序。

    (→) 逆否：ρ 非全序给出互不可达对，G34d 构造两个不同的相容序，
        与唯一性矛盾。
    (←) ρ 全序：任何相容序都等于 ρ（G34c / G29a）。

    于是 G29 的二分成为全模型的定理：**因果层的自由度恰且仅由
    「存在 ρ-不可比事件」产生**。注意前提 hno 恰是层存在性条件
    （G34-pre）；右作用元模型上根本没有相容序，唯一性空洞成立。 -/
theorem causal_order_unique_iff_reach_total {M C : Type*} (A : AxiomA M C)
    (hno : ∀ x y : C, A.compose x y ≠ x) :
    (∀ r : C → C → Prop,
        (∀ x : C, ¬ r x x) → (∀ x y z : C, r x y → r y z → r x z) →
        (∀ α β : C, r α (A.compose α β)) →
        ∀ x y : C, r x y ↔ oneStepReach A x y) ↔
    (∀ x y : C, x ≠ y → oneStepReach A x y ∨ oneStepReach A y x) := by
  constructor
  · intro hunique
    by_contra hnt
    push_neg at hnt
    obtain ⟨x₀, y₀, hne, h₁, h₂⟩ := hnt
    -- push_neg 把 ¬∃ 推成 ∀ γ, … → …；转回 ¬ρ 形状
    have i₁ : ¬ oneStepReach A x₀ y₀ := by
      rintro ⟨γ, hγ, hne'⟩
      exact hne' (h₁ γ hγ)
    have i₂ : ¬ oneStepReach A y₀ x₀ := by
      rintro ⟨γ, hγ, hne'⟩
      exact hne' (h₂ γ hγ)
    obtain ⟨r₁, r₂, hi₁, ht₁, hc₁, hi₂, ht₂, hc₂, hr₂, hnr₁⟩ :=
      compatible_order_not_unique_of_reach_not_total A hno hne i₁ i₂
    have h₁' : ∀ x y : C, r₁ x y ↔ oneStepReach A x y := hunique r₁ hi₁ ht₁ hc₁
    have h₂' : ∀ x y : C, r₂ x y ↔ oneStepReach A x y := hunique r₂ hi₂ ht₂ hc₂
    exact hnr₁ ((h₁' x₀ y₀).mpr ((h₂' x₀ y₀).mp hr₂))
  · intro htotal r hi ht hc x y
    exact eq_reach_of_reach_total (A := A) (r := r) hi ht hc htotal x y

/-- 相容严格偏序升格为因果-振幅层：`causalOrder` 字段**定义地**等于 r。
    这是 `nonempty_layer_iff_exists_compatible_order`（G6d）反方向的
    非封装形式——不用 Nonempty 包装，投影可直接还原 r
    （phase_compat 由既有 `phase_compat_of_causal_fields` 填充）。 -/
def compatibleOrderLayer {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    {r : C → C → Prop}
    (hirrefl : ∀ x : C, ¬ r x x)
    (htrans : ∀ x y z : C, r x y → r y z → r x z)
    (hcompat : ∀ α β : C, r α (A.compose α β)) :
    V1CausalAmplitudeLayer (M := M) (C := C) where
  causalOrder := r
  irrefl := hirrefl
  trans := htrans
  compat := hcompat
  phase_compat := phase_compat_of_causal_fields hirrefl hcompat

/-- **G34f（W1，A 档，主定理·层级）**：在无右作用元（且承载 AxiomC）的
    模型上，因果-振幅层的因果序唯一 **⟺** 可达序 ρ 全序。

    (→) 层给出相容序（G6 提取）；关系级唯一性经 G34e 升级为全序。
        任意相容序经 `compatibleOrderLayer` 升格为层，其 `causalOrder`
        定义地等于该序。
    (←) 层的因果序是相容序，直接由 G29a 等于 ρ。

    G29b/G29c/G29d（见证模型因果序唯一）成为本定理在
    `witnessReach_total` 下的实例。 -/
theorem layer_order_unique_iff_reach_total {M C : Type*}
    [A : AxiomA M C] [Cx : AxiomC M C]
    (hno : ∀ x y : C, A.compose x y ≠ x) :
    (∀ L : V1CausalAmplitudeLayer (M := M) (C := C),
        ∀ x y : C, L.causalOrder x y ↔ oneStepReach A x y) ↔
    (∀ x y : C, x ≠ y → oneStepReach A x y ∨ oneStepReach A y x) := by
  constructor
  · intro hlay
    apply (causal_order_unique_iff_reach_total A hno).mp
    intro r hi ht hc x y
    exact hlay (compatibleOrderLayer hi ht hc) x y
  · intro htotal L x y
    exact eq_reach_of_reach_total (A := A) (r := L.causalOrder)
      L.irrefl L.trans L.compat htotal x y

/-! ============================================================================
    §6. G34g：典范模型实例化（二分的两侧各落一个）
   ============================================================================ -/

/-- **G34g-1（W1，A 档）**：见证模型满足二分的「唯一」侧：
    任何相容严格偏序都逐点等于 ρ（= `<`，由 `witnessReach_iff_lt`）。

    这是 G29b 的一般定理重述：不再引用见证模型的具体性质，
    只用 `witnessReach_total`（G16c）作为全序性输入。 -/
theorem witness_order_unique_general :
    ∀ r : ℕ → ℕ → Prop,
      (∀ x : ℕ, ¬ r x x) → (∀ x y z : ℕ, r x y → r y z → r x z) →
      (∀ α β : ℕ, r α (witnessAxiomA.compose α β)) →
      ∀ x y : ℕ, r x y ↔ oneStepReach witnessAxiomA x y := by
  apply (causal_order_unique_iff_reach_total witnessAxiomA witness_no_right_id).mpr
  exact witnessReach_total

/-- **G34g-2（W1，A 档）**：乘积模型满足二分的「不唯一」侧：
    存在两个相容严格偏序与一对点使它们不等。

    这是 G30c 的关系级重述：不引用 `pairE1`/`pairE2` 的具体构造，
    只用 `pairReach_not_total`（G17d）经反证提取互不可达对，
    再由 G34d 一般构造第二序。 -/
theorem pair_relation_order_not_unique :
    ∃ (r₁ r₂ : PairRule → PairRule → Prop) (u v : PairRule),
      (∀ x : PairRule, ¬ r₁ x x) ∧ (∀ x y z : PairRule, r₁ x y → r₁ y z → r₁ x z) ∧
      (∀ α β : PairRule, r₁ α (pairAxiomA.compose α β)) ∧
      (∀ x : PairRule, ¬ r₂ x x) ∧ (∀ x y z : PairRule, r₂ x y → r₂ y z → r₂ x z) ∧
      (∀ α β : PairRule, r₂ α (pairAxiomA.compose α β)) ∧
      r₂ u v ∧ ¬ r₁ u v := by
  have h := pairReach_not_total
  push_neg at h
  obtain ⟨u, v, hne, h₁, h₂⟩ := h
  obtain ⟨r₁, r₂, hi₁, ht₁, hc₁, hi₂, ht₂, hc₂, hr₂, hnr₁⟩ :=
    compatible_order_not_unique_of_reach_not_total (A := pairAxiomA)
      pair_no_right_id hne h₁ h₂
  exact ⟨r₁, r₂, u, v, hi₁, ht₁, hc₁, hi₂, ht₂, hc₂, hr₂, hnr₁⟩

end CSQIT_V1Bridge
