/-
================================================================================
CSQIT_V1Bridge — 第十轮：因果层刚性（G29–G32）
模块: CSQIT_V1Bridge.OrderRigidity
版本: v0.1.0（2026-11-08）
================================================================================

上一轮（G26–G28）闭合了见证模型上 AxiomC 空间的完整分类，留下两个与
「因果层能否成为独立结构层」直接相关的缺口：

  (1) G9 只说了「可达序是所有相容严格偏序中最小的」，没有回答
      **相容序是否唯一**。若唯一，则因果层在该模型上不是自由度，
      而是被 compose 完全钉死；若不唯一，它才真正是独立结构层。
      本模块给出**二分**：
        · 一般定理（A 档）：若可达序全序，则相容严格偏序唯一 = 可达序。
        · 见证模型（A 档）：可达序 = `<`，全序，故因果序唯一。
        · 乘积模型（A 档）：可达序非全序，且可显式构造第二个相容序，
          故因果序不唯一。
      结论：**因果层的自由度恰由「时空中存在不可比较事件」产生**；
      在全序模型上因果层是冗余结构，在分支模型上才是独立选择。

  (2) V1 的 RG 流（A2）在 v23 中的最小翻译是自同态。G12/G21 已给出
      「保振幅自同态 = 恒等」。本模块补上三件事：
        · 每个自同态都严格单调，因而**保持因果序**（序嵌入）；
        · 保振幅自同态只有恒等（强化 G12 的表述）；
        · 满射自同态只有恒等 —— 不存在非平凡的「粗粒化」流。
      结论：**因果序对全部 RG 流不变，振幅只对恒等流不变，且流不可能满射**。

判定档位：本文件所有定理均为 A 档（可证，无新增公设）。
纪律：零新增 axiom、零 sorry；不修改 CSQIT_W1 / CSQIT_Enhanced /
      既有 V1Bridge 文件；只新增本文件与 lakefile 两行。
================================================================================ -/

import CSQIT_V1Bridge.CausalSetWitness
import CSQIT_V1Bridge.NonTotalModel
import CSQIT_V1Bridge.GaugeAndEndo

namespace CSQIT_V1Bridge

open CSQIT_W1.CompilerAxioms
open CSQIT_W1.Foundation

/-! ============================================================================
    §1. G29：一般刚性定理 —— 可达序全序 ⇒ 相容序唯一
   ============================================================================ -/

/-- **G29a（W1，A 档）**：若可达关系在所有不同点对上至少有一个方向成立
    （即「可达序」作为二分关系是全的），则任何相容严格偏序都恰等于可达关系。

    证明：
      · `←` 方向由相容性 `r α (α∘β)` 直接得到；
      · `→` 方向：若 `r x y` 且 `y ≠ x`，全序性给出 `x ≺ y` 或 `y ≺ x`；
        后者连同 `r x y` 经传递性给出 `r x x`，与反自反矛盾。

    这是纯 `AxiomA` 层面的结论，不需要 `AxiomC`。 -/
theorem eq_reach_of_reach_total {M C : Type*} [A : AxiomA M C]
    {r : C → C → Prop}
    (hirrefl : ∀ x : C, ¬ r x x)
    (htrans : ∀ x y z : C, r x y → r y z → r x z)
    (hcompat : ∀ a b : C, r a (A.compose a b))
    (hreach_total : ∀ x y : C, x ≠ y →
      (∃ z : C, y = A.compose x z ∧ y ≠ x) ∨
      (∃ z : C, x = A.compose y z ∧ x ≠ y)) :
    ∀ x y : C, r x y ↔ ∃ z : C, y = A.compose x z ∧ y ≠ x := by
  intro x y
  constructor
  · intro hxy
    by_cases hyx : x = y
    · exact absurd (hyx ▸ hxy) (hirrefl y)
    · rcases hreach_total x y hyx with ⟨z, hz, hne⟩ | ⟨z, hz, hne⟩
      · exact ⟨z, hz, hne⟩
      · have hy : r y (A.compose y z) := hcompat y z
        have hyx' : r y x := by rw [hz]; exact hy
        exact absurd (htrans x y x hxy hyx') (hirrefl x)
  · rintro ⟨z, hz, hne⟩
    have hxz : r x (A.compose x z) := hcompat x z
    rwa [← hz] at hxz

/-! ============================================================================
    §2. G29b：见证模型上因果序唯一
   ============================================================================ -/

/-- **G29b（W1，A 档）**：见证模型上任何相容严格偏序都等于可达序 `<`。

    全序性取自既有定理 `witnessReach_total`（G16d-0）。

    即：以 `compose a b = a + b + 1` 为合成、满足反自反/传递/
    相容三条的序关系只有一个。 -/
theorem witness_order_unique {r : ℕ → ℕ → Prop}
    (hirrefl : ∀ x : ℕ, ¬ r x x)
    (htrans : ∀ x y z : ℕ, r x y → r y z → r x z)
    (hcompat : ∀ a b : ℕ, r a (witnessAxiomA.compose a b)) :
    ∀ a b : ℕ, r a b ↔ witnessReach a b :=
  eq_reach_of_reach_total (A := witnessAxiomA) (r := r)
    hirrefl htrans hcompat witnessReach_total

/-- **G29c（W1，A 档）**：见证模型上任意 V1 因果-振幅层的因果序都等于 `<`。

    因此在该模型上，因果层不是独立自由度：一旦 `AxiomA` 的 compose
    固定，因果序被唯一钉死。 -/
theorem witness_layer_order_unique
    (layer : V1CausalAmplitudeLayer (M := ℕ) (C := ℕ)) :
    ∀ a b : ℕ, layer.causalOrder a b ↔ witnessReach a b :=
  eq_reach_of_reach_total (A := witnessAxiomA) (r := layer.causalOrder)
    layer.irrefl layer.trans layer.compat witnessReach_total

/-- **G29d（W1，A 档）**：见证模型上两个因果-振幅层必有相同因果序。

    即「振幅参数可以不同，因果序不可能不同」。 -/
theorem witness_two_layers_same_order
    (L₁ L₂ : V1CausalAmplitudeLayer (M := ℕ) (C := ℕ)) :
    ∀ a b : ℕ, L₁.causalOrder a b ↔ L₂.causalOrder a b := by
  intro a b
  rw [witness_layer_order_unique L₁ a b, witness_layer_order_unique L₂ a b]

/-! ============================================================================
    §3. G30：乘积模型上因果序不唯一（非全序 ⇒ 出现自由度）
   ============================================================================ -/

/-- 乘积模型中的极小元 `(1,0)`。 -/
def pairE1 : PairRule := ⟨(1, 0), by simp⟩

/-- 乘积模型中的极小元 `(0,1)`。 -/
def pairE2 : PairRule := ⟨(0, 1), by simp⟩

theorem pairE1_ne_pairE2 : pairE1 ≠ pairE2 := by
  intro h
  have h1 : pairE1.val.1 = pairE2.val.1 := congrArg (fun p : PairRule => p.val.1) h
  simp [pairE1, pairE2] at h1

/-- `(1,0)` 没有任何严格前驱：乘积偏序中 `u ≤ (1,0)` 且 `u ≠ (1,0)`
    迫使 `u = (0,0)`，而后者不在载体中。 -/
theorem not_pairReach_e1 (u : PairRule) : ¬ pairReach u pairE1 := by
  intro h
  rw [pairReach_iff] at h
  obtain ⟨h1, h2, hne⟩ := h
  simp [pairE1] at h1 h2
  have hu2 : u.val.2 = 0 := by omega
  have hu1ne : u.val.1 ≠ 0 := by
    intro hz
    exact u.property (Prod.ext hz hu2)
  have hu1 : u.val.1 = 1 := by omega
  exact hne (Subtype.ext (Prod.ext hu1 hu2))

/-- **G30a（W1，A 档）**：`(1,0)` 与 `(0,1)` 在可达序下不可比较。 -/
theorem not_pairReach_e1_e2 : ¬ pairReach pairE1 pairE2 := by
  intro h
  rw [pairReach_iff] at h
  obtain ⟨h1, _, _⟩ := h
  simp [pairE1, pairE2] at h1

/-- 在可达序上**只加一条边** `(1,0) ≺ (0,1)` 并取传递闭包所得的关系。

    显式形式：`u ≺ v`，或 `u = (1,0)` 且 `(v = (0,1)` 或 `(0,1) ≺ v)`。
    由于 `(0,1) ≺ v` 与 `v = (0,1)` 的并恰是 `(0,1)` 的上闭包，
    这个关系对传递性封闭（见 `pairAltOrder_trans`）。 -/
def pairAltOrder (u w : PairRule) : Prop :=
  pairReach u w ∨ (u = pairE1 ∧ (w = pairE2 ∨ pairReach pairE2 w))

theorem pairAltOrder_irrefl (u : PairRule) : ¬ pairAltOrder u u := by
  rintro (h | ⟨hu, hw | hw⟩)
  · exact pairReach_irrefl u h
  · exact pairE1_ne_pairE2 (hu.symm.trans hw)
  · exact not_pairReach_e1 pairE2 (hu ▸ hw)

theorem pairAltOrder_trans {u v w : PairRule}
    (huv : pairAltOrder u v) (hvw : pairAltOrder v w) : pairAltOrder u w := by
  rcases huv with h1 | ⟨hu, hv⟩
  · rcases hvw with h2 | ⟨hv', _⟩
    · exact Or.inl (pairReach_trans h1 h2)
    · exact absurd (hv' ▸ h1) (not_pairReach_e1 u)
  · rcases hvw with h2 | ⟨hv', _⟩
    · rcases hv with hve | hvr
      · subst hve
        exact Or.inr ⟨hu, Or.inr h2⟩
      · exact Or.inr ⟨hu, Or.inr (pairReach_trans hvr h2)⟩
    · rcases hv with hve | hvr
      · exact absurd (hv'.symm.trans hve) pairE1_ne_pairE2
      · exact absurd (hv' ▸ hvr) (not_pairReach_e1 pairE2)

theorem pairAltOrder_compat (α β : PairRule) :
    pairAltOrder α (pairCompose α β) :=
  Or.inl (pairReach_compat α β)

/-- **G30b（W1，A 档）**：乘积模型上的第二个相容因果-振幅层。 -/
def pairAltLayer : V1CausalAmplitudeLayer (M := Unit) (C := PairRule) where
  causalOrder := pairAltOrder
  irrefl := pairAltOrder_irrefl
  trans := fun _ _ _ => pairAltOrder_trans
  compat := pairAltOrder_compat
  phase_compat := phase_compat_of_causal_fields pairAltOrder_irrefl pairAltOrder_compat

/-- **G30c（W1，A 档）**：乘积模型上存在两个因果序不同的因果-振幅层。

    这是 G29「全序 ⇒ 唯一」的互补面：当可达序非全序时，
    可以在不可比较点上加入额外关系，得到严格更细的相容序。
    故因果层是否是独立结构层，**取决于模型是否分支**。 -/
theorem pair_causal_order_not_unique :
    ∃ (L₁ L₂ : V1CausalAmplitudeLayer (M := Unit) (C := PairRule)),
      ∃ u v : PairRule, L₁.causalOrder u v ∧ ¬ L₂.causalOrder u v :=
  ⟨pairAltLayer, pairLayer, pairE1, pairE2,
    Or.inr ⟨rfl, Or.inl rfl⟩, not_pairReach_e1_e2⟩

/-- **G30d（W1，A 档）**：因果序唯一性的完整二分（在两个典范模型上）。

    · 见证模型（可达序全序）：任意两个层的因果序相同；
    · 乘积模型（可达序非全序）：存在两个层因果序不同。 -/
theorem causal_order_uniqueness_dichotomy :
    (∀ L₁ L₂ : V1CausalAmplitudeLayer (M := ℕ) (C := ℕ),
        ∀ a b : ℕ, L₁.causalOrder a b ↔ L₂.causalOrder a b) ∧
    (∃ (L₁ L₂ : V1CausalAmplitudeLayer (M := Unit) (C := PairRule)),
        ∃ u v : PairRule, L₁.causalOrder u v ∧ ¬ L₂.causalOrder u v) :=
  ⟨witness_two_layers_same_order, pair_causal_order_not_unique⟩

/-! ============================================================================
    §4. G31：RG 流 —— 全部自同态保持因果序，只有恒等保持振幅
   ============================================================================ -/

/-- **G31a（W1，A 档）**：见证模型的每个自同态都严格单调。 -/
theorem witnessEndo_strictMono (φ : ℕ → ℕ)
    (h : ∀ a b : ℕ, φ (a + b + 1) = φ a + φ b + 1) :
    StrictMono φ := by
  intro a b hab
  rw [witnessEndo_classification φ h a, witnessEndo_classification φ h b]
  have hpos : 0 < φ 0 + 1 := Nat.succ_pos _
  have hmul : a * (φ 0 + 1) < b * (φ 0 + 1) :=
    Nat.mul_lt_mul_of_pos_right hab hpos
  omega

/-- **G31b（W1，A 档）**：自同态把因果序反射回来，即 `φ` 是序嵌入。 -/
theorem witnessEndo_order_iff (φ : ℕ → ℕ)
    (h : ∀ a b : ℕ, φ (a + b + 1) = φ a + φ b + 1) (a b : ℕ) :
    φ a < φ b ↔ a < b := by
  constructor
  · intro hlt
    rcases Nat.lt_trichotomy a b with h' | h' | h'
    · exact h'
    · subst h'
      exact absurd hlt (lt_irrefl _)
    · have := witnessEndo_strictMono φ h h'
      omega
  · intro hlt
    exact witnessEndo_strictMono φ h hlt

/-- **G31c（W1，A 档）**：每个自同态都保持典范因果序（可达序）。 -/
theorem witnessEndo_preserves_causal_order (φ : ℕ → ℕ)
    (h : ∀ a b : ℕ, φ (a + b + 1) = φ a + φ b + 1) (a b : ℕ) :
    witnessReach a b ↔ witnessReach (φ a) (φ b) := by
  rw [witnessReach_iff_lt, witnessReach_iff_lt, witnessEndo_order_iff φ h]

/-- **G31d（W1，A 档）**：保振幅的自同态只有恒等。

    G12/G21 已给出「保振幅 ↔ φ 0 = 0」；结合分类定理
    `φ n = φ 0 + n(φ 0 + 1)`，φ 0 = 0 迫使 `φ n = n`。 -/
theorem witnessEndo_amplitude_preserving_eq_id (φ : ℕ → ℕ)
    (h : ∀ a b : ℕ, φ (a + b + 1) = φ a + φ b + 1)
    (hamp : ∀ n : ℕ, witnessAxiomC.amplitude (φ n) = witnessAxiomC.amplitude n) :
    φ = id := by
  have h0 : φ 0 = 0 := (witnessEndo_amplitude_iff φ h).1 hamp
  funext n
  rw [witnessEndo_classification φ h n, h0]
  simp

/-- **G31e（W1，A 档）**：满射自同态只有恒等 —— 不存在非平凡的粗粒化流。

    证明：满射给出 `φ n₀ = 0`，分类式两项非负迫使 `φ 0 = 0`，
    再由分类式得 `φ n = n`。 -/
theorem witnessEndo_surjective_eq_id (φ : ℕ → ℕ)
    (h : ∀ a b : ℕ, φ (a + b + 1) = φ a + φ b + 1)
    (hsurj : Function.Surjective φ) : φ = id := by
  obtain ⟨n₀, hn₀⟩ := hsurj 0
  have hcls := witnessEndo_classification φ h n₀
  rw [hcls] at hn₀
  have h0 : φ 0 = 0 := (Nat.add_eq_zero_iff.mp hn₀).1
  funext n
  rw [witnessEndo_classification φ h n, h0]
  simp

/-- **G32（W1，A 档）**：RG 流结构总结。

    在见证模型上：
      1. 每个自同态都是严格单调的（因而是因果序嵌入）；
      2. 每个自同态都保持因果序 `≺`；
      3. 保振幅的自同态只有恒等；
      4. 满射自同态只有恒等。

    读法：**因果序对全部 RG 流不变，振幅只对恒等流不变；
    并且流永远不能满射**。这把 V1 A2（RG 流）与 A3（因果性）、
    A4（振幅）的关系压缩为一条可证的结构陈述。 -/
theorem rg_flow_structure :
    (∀ (φ : ℕ → ℕ), (∀ a b : ℕ, φ (a + b + 1) = φ a + φ b + 1) → StrictMono φ) ∧
    (∀ (φ : ℕ → ℕ), (∀ a b : ℕ, φ (a + b + 1) = φ a + φ b + 1) →
        ∀ a b : ℕ, witnessReach a b ↔ witnessReach (φ a) (φ b)) ∧
    (∀ (φ : ℕ → ℕ), (∀ a b : ℕ, φ (a + b + 1) = φ a + φ b + 1) →
        (∀ n : ℕ, witnessAxiomC.amplitude (φ n) = witnessAxiomC.amplitude n) → φ = id) ∧
    (∀ (φ : ℕ → ℕ), (∀ a b : ℕ, φ (a + b + 1) = φ a + φ b + 1) →
        Function.Surjective φ → φ = id) :=
  ⟨witnessEndo_strictMono,
   witnessEndo_preserves_causal_order,
   witnessEndo_amplitude_preserving_eq_id,
   witnessEndo_surjective_eq_id⟩

end CSQIT_V1Bridge
