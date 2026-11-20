/-
================================================================================
CSQIT_V1Bridge — v23 结构的三条硬边界（第十三轮）
模块: CSQIT_V1Bridge.StructuralLimits
版本: v0.1.0（2026-11-07）
================================================================================

承 `D:\CSQIT历史脉络\23_路径结论.md` §10（G8–G11）。上一轮已把
「V1 因果-振幅层」收口为：
  · 振幅层 S 由 amplitude 唯一导出（A，G4/G10）；
  · 层存在 ⟺ 无右作用元，且载体必无限（A，G6/G7/G8）；
  · 可达序是所有相容序的最小者（A，G9）。
本轮往下做三条**新的可证边界**，全部零新增公设：

  §1 G12（A，否定）RG 保振幅平凡性：
    任何满足 `amplitude (φ α) = amplitude α` 的自映射 φ 必为恒等
    （由 `AxiomC.amplitude_injective` 直接推出）。
    结构性后果：若把「RG 固定点」实现为「保持作用量/振幅不变的
    规则自映射」，则在 v23 中不存在非平凡的固定点流；尺度作用只可能
    是恒等。V1 A2 的完整 RG 语义（粗粒化、耦合跑动）仍需尺度参数
    与重整化算子，属 C 档；本定理只否定**振幅层上的非平凡实现**。

  §2 G14（A，结构）任意层的定向性：
    v23 已证 `amplitude` 单射 ⇒ `compose` 交换
    （`TwoAspectNoFinite.amplitude_injective_implies_compose_comm`）。
    由此，任何 `V1CausalAmplitudeLayer` 的因果序满足：
      (a) 每对元素有共同上界 `α∘β`（向上定向）；
      (b) 每个元素都有后继，故无极大元；
      (c) 每个复合 `α∘β` 同时以 α 与 β 为前驱。
    这说明该因果层**不带方向信息**：α 与 β 都先于 α∘β，
    无法由 compose 区分「先 α 后 β」与「先 β 后 α」。

  §3 G15（A，否定接口）边界通道退化：
    `CompilerAxiom` 的 `core_collapse` 与 `AxiomA` 的
    `CoreCollapse.input_must_be_empty` 都强制 `input ≡ []`。
    因此任何**只依赖 input** 的「边界 → 体」映射是常值，在非平凡规则集
    上必不可单射。V1 A1（全息涌现：边界完全决定体）在 v23 的唯一
    边界通道上不可实现。A1 的整体语义（C*-代数等距同构）仍为 C 档。

纪律：零新增 axiom、零 sorry；只 import 既有模块；
      不修改 CSQIT_W1 / CSQIT_Enhanced / 既有 V1Bridge 文件。
================================================================================ -/

import CSQIT_W1.CompilerAxioms
import CSQIT_W1.Foundation
import CSQIT_W1.CoreCollapse
import CSQIT_W1.TwoAspectNoFinite
import CSQIT_V1Bridge.CausalAmplitudeLayer
import CSQIT_V1Bridge.OrderAndFixedPoint

namespace CSQIT_V1Bridge

open CSQIT_W1.CompilerAxioms
open CSQIT_W1.Foundation
open CSQIT_W1.TwoAspectNoFinite

/-! ============================================================================
    §1. G12：RG 保振幅平凡性（A 档，否定）
   ============================================================================ -/

/-- **保振幅映射**：φ 不改变每条规则的振幅。
    这是「RG 固定点保持有效作用量」在 v23 振幅层上的最小翻译。 -/
def AmplitudePreserving {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (φ : C → C) : Prop :=
  ∀ α : C, Cx.amplitude (φ α) = Cx.amplitude α

/-- **G12（W1，A 档）**：保振幅映射逐点等于恒等。
    证明只用 `AxiomC.amplitude_injective`：若 `amp (φ α) = amp α`，
    则由单射立即得 `φ α = α`。 -/
theorem amplitude_preserving_apply_eq_self {M C : Type*} [A : AxiomA M C]
    [Cx : AxiomC M C] (φ : C → C) (h : AmplitudePreserving (M := M) φ) (α : C) :
    φ α = α :=
  Cx.amplitude_injective (h α)

/-- **G12（W1，A 档）**：保振幅映射作为函数等于恒等。 -/
theorem amplitude_preserving_eq_id {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (φ : C → C) (h : AmplitudePreserving (M := M) φ) : φ = id :=
  funext (amplitude_preserving_apply_eq_self (M := M) φ h)

/-- **G12（W1，A 档，尺度作用版）**：任意参数族 `ρ s` 若每个都保振幅，
    则该参数族是恒等常族。特别地，一个以「保作用量」为固定点条件的
    尺度半群作用，在振幅层上只能是平凡作用。

    注意：这里**不要求** `S` 是幺半群、`ρ` 是作用；结论对任意参数类型成立，
    因此对「RG 流」的通常定义（幺半群作用）自动成立。 -/
theorem amplitude_scale_action_trivial {M C S : Type*} [A : AxiomA M C]
    [Cx : AxiomC M C] (ρ : S → C → C) (h : ∀ s : S, AmplitudePreserving (M := M) (ρ s)) :
    ∀ s : S, ρ s = id := fun s => amplitude_preserving_eq_id (M := M) (ρ s) (h s)

/-- **G12（W1，A 档）**：振幅层的对称群是平凡的——
    保振幅的自映射构成单元素类型。 -/
theorem amplitude_symmetry_subsingleton {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C] :
    Subsingleton {φ : C → C // AmplitudePreserving (M := M) φ} := by
  constructor
  rintro ⟨f, hf⟩ ⟨g, hg⟩
  apply Subtype.ext
  funext α
  exact (amplitude_preserving_apply_eq_self (M := M) f hf α).trans
    (amplitude_preserving_apply_eq_self (M := M) g hg α).symm

/-! ============================================================================
    §2. G14：任意因果层的定向性（A 档，结构）
   ============================================================================ -/

/-- **v23 的组合交换性（无条件版，W1，A 档）**：
    `AxiomC` 的振幅单射字段使 `compose` 在**每个**合法模型上交换。

    这条把 `TwoAspectNoFinite` 的条件定理（显式 `h_inj` 前提）实例化为
    `AxiomC` 模型上的无条件结论；V1Bridge 后续各层都可用它。 -/
theorem compose_comm_of_axiomC {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α β : C) : A.compose α β = A.compose β α :=
  amplitude_injective_implies_compose_comm Cx.amplitude_injective α β

/-- **G14（W1，A 档）**：层中任一复合 `α∘β` 同时是 α 与 β 的上界。 -/
theorem layer_common_upper_bound {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (layer : V1CausalAmplitudeLayer (M := M) (C := C)) (α β : C) :
    layer.causalOrder α (A.compose α β) ∧ layer.causalOrder β (A.compose α β) := by
  constructor
  · exact layer.compat α β
  · have h := layer.compat β α
    rwa [← compose_comm_of_axiomC α β] at h

/-- **G14（W1，A 档）**：层序向上定向——任意两元素有共同上界。
    因此该因果序不是任意偏序，而是定向偏序；但它仍可非全序
    （见 `CausalSetWitness` 的乘积模型）。 -/
theorem layer_upward_directed {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (layer : V1CausalAmplitudeLayer (M := M) (C := C)) (α β : C) :
    ∃ γ : C, layer.causalOrder α γ ∧ layer.causalOrder β γ :=
  ⟨A.compose α β, layer_common_upper_bound layer α β⟩

/-- **G14（W1，A 档）**：层中无幂等元——`α∘α ≠ α`。
    若 `α∘α = α`，`compat` 与 `irrefl` 立即矛盾。 -/
theorem layer_compose_self_ne {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (layer : V1CausalAmplitudeLayer (M := M) (C := C)) (α : C) :
    A.compose α α ≠ α := by
  intro h
  have hc : layer.causalOrder α (A.compose α α) := layer.compat α α
  rw [h] at hc
  exact layer.irrefl α hc

/-- **G14（W1，A 档）**：层中每个元素都有非平凡后继，故无极大元。
    后继取 `α∘α`，且由 `layer_compose_self_ne` 知它与 α 不同。 -/
theorem layer_no_maximal {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (layer : V1CausalAmplitudeLayer (M := M) (C := C)) (α : C) :
    ∃ β : C, β ≠ α ∧ layer.causalOrder α β :=
  ⟨A.compose α α, layer_compose_self_ne layer α, layer.compat α α⟩

/-- **G14（W1，A 档）**：层的因果步没有「唯一前驱」。
    每个复合 `α∘β` 同时以 α 与 β 为前驱；当 `α ≠ β` 时，
    同一个后果有两个不同的直接前驱。

    这是「方向信息缺失」的精确形式：`compose` 交换，故无法仅凭
    复合关系把「α 先于 β」与「β 先于 α」区分开。 -/
theorem layer_step_two_predecessors {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (layer : V1CausalAmplitudeLayer (M := M) (C := C)) {α β : C} (hne : α ≠ β) :
    α ≠ β ∧ layer.causalOrder α (A.compose α β) ∧
    layer.causalOrder β (A.compose α β) :=
  ⟨hne, layer_common_upper_bound layer α β⟩

/-! ============================================================================
    §3. G15：边界通道退化（A 档，接口否定）
   ============================================================================ -/

/-- **CompilerAxiom 版边界常值（W1，A 档）**：
    任意两条规则的 input 列表相同（都为空）。 -/
theorem boundary_input_constant {M C : Type*} [CA : CompilerAxiom M C] (α β : C) :
    CA.input α = CA.input β := by
  rw [core_collapse α, core_collapse β]

/-- **CompilerAxiom 版（W1，A 档）**：`input` 不是单射。
    非平凡规则集上，边界数据无法区分规则。 -/
theorem boundary_input_not_injective {M C : Type*} [CA : CompilerAxiom M C] [Nontrivial C] :
    ¬ Function.Injective CA.input := by
  rintro h
  obtain ⟨a, b, hab⟩ := exists_pair_ne C
  exact hab (h (boundary_input_constant a b))

/-- **只依赖边界的映射必为常值（W1，A 档）**：
    若 `h = g ∘ input`，则 h 在任意两条规则上取同值。
    这是「边界 → 体」映射的退化形式：边界通道 `input` 恒空，
    故任何经由此通道的映射都不携带规则信息。 -/
theorem boundary_determined_constant {M C X : Type*} [CA : CompilerAxiom M C]
    (h : C → X) (hh : ∃ g : List M → X, ∀ c : C, h c = g (CA.input c)) :
    ∀ a b : C, h a = h b := by
  obtain ⟨g, hg⟩ := hh
  intro a b
  rw [hg a, hg b, boundary_input_constant a b]

/-- **边界决定的映射在非平凡规则集上不可单射（W1，A 档）**：
    V1 A1「边界完全决定体」若只经 `input` 通道实现，则体映射必为常值，
    因而不能是单射。 -/
theorem boundary_determined_not_injective {M C X : Type*} [CA : CompilerAxiom M C]
    [Nontrivial C] (h : C → X)
    (hh : ∃ g : List M → X, ∀ c : C, h c = g (CA.input c)) :
    ¬ Function.Injective h := by
  rintro hinj
  obtain ⟨a, b, hab⟩ := exists_pair_ne C
  exact hab (hinj (boundary_determined_constant h hh a b))

/-- **AxiomA 版边界常值（W1，A 档）**：
    `CoreCollapse.input_must_be_empty` 对 AxiomA 同样强制 `input ≡ []`。 -/
theorem causal_boundary_constant {M C : Type*} [A : AxiomA M C] (α β : C) :
    A.input α = A.input β := by
  rw [CSQIT_W1.CoreCollapse.input_must_be_empty α,
      CSQIT_W1.CoreCollapse.input_must_be_empty β]

/-- **AxiomA 版边界决定的映射不可单射（W1，A 档）**。 -/
theorem causal_boundary_determined_not_injective {M C X : Type*} [A : AxiomA M C]
    [Nontrivial C] (h : C → X)
    (hh : ∃ g : List M → X, ∀ c : C, h c = g (A.input c)) :
    ¬ Function.Injective h := by
  rintro hinj
  obtain ⟨a, b, hab⟩ := exists_pair_ne C
  have hconst : ∀ a b : C, h a = h b := by
    obtain ⟨g, hg⟩ := hh
    intro p q
    rw [hg p, hg q, causal_boundary_constant p q]
  exact hab (hinj (hconst a b))

end CSQIT_V1Bridge
