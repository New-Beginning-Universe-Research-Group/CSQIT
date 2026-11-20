/-
================================================================================
CSQIT_V1Bridge — V1 因果-振幅独立结构层
模块: CSQIT_V1Bridge.CausalAmplitudeLayer
版本: v0.1.0（2026-11-06）
================================================================================

回答用户重点问题 #2：「V1 的因果性与振幅层能否作为独立结构层架在 v23 之上」。

结论（四档）：
  · 振幅层 S : C → Real.Angle  —— A（可由 AxiomC 导出，见 OrderAndAction G4）
  · 因果偏序（与 compose 相容）  —— B（不可均匀导出；无右单位元模型上可构造）
  · 二者组合为独立层            —— B（在无右单位元模型类上可构造，且因果-相位
                                   相容定理成立；不可均匀构造，见 no-go）

本模块做三件事：

  §1 定义独立结构 `V1CausalAmplitudeLayer`：
      架在 v23 的 [AxiomA M C] + [AxiomC M C] 之上，不改任何既有字段。
      字段：
        (a) causalOrder : C → C → Prop，严格偏序且与 compose 相容
        (b) 相位 actionPhase（复用 G4 的定义，不重写）
        (c) 因果-相位相容：α ≺ β 且 β = α∘γ ⇒ actionPhase γ ≠ 0

  §2 可构造性（无右单位元模型类）：
      取 G1 的条件序 `α ≺ β := ∃ γ, β = α∘γ ∧ β ≠ α`，
      则它与 G4 的 actionPhase 一起满足 §1 的全部字段。
      关键引理：无右单位元 ⇒ 不存在 γ 使 amplitude γ = 1
      （否则 γ 是右单位元，由 amplitude_injective 推出）。

  §3 no-go 与共存见证：
      no-go：不存在对所有模型都成立的 uniform 层（复用 G1）。
      共存：Enhanced 的 Fin 7 模型里 output=id、amplitude=7 次单位根、
      因果序=标准序同时非平凡——但该序是 AxiomB' 外加字段，不是导出的。

纪律：零新增 axiom、零 sorry；只 import 既有模块（CompilerAxioms、
      Foundation、OrderAndAction）；不修改 CSQIT_W1 / CSQIT_Enhanced /
      CSQIT_V1Bridge 的其他文件。
================================================================================ -/

import CSQIT_W1.CompilerAxioms
import CSQIT_W1.Foundation
import CSQIT_V1Bridge.OrderAndAction
import CSQIT_V1Bridge.OrderAndFixedPoint

namespace CSQIT_V1Bridge

open CSQIT_W1.CompilerAxioms
open CSQIT_W1.Foundation
open Complex

/-! ============================================================================
    §1. 独立结构层定义
   ============================================================================ -/

/-- **V1 因果-振幅层**：架在 v23 的 `AxiomA` + `AxiomC` 之上的独立结构。

    不修改任何既有字段；只新增一个因果序 `causalOrder`，并要求它与
    `AxiomC.amplitude` 导出的相位 `actionPhase` 相容。

    字段说明：
      · `causalOrder`：C 上的二元关系，要求是严格偏序（反自反 + 传递）
      · `compat`：对任意 α β，有 `α ≺ α∘β`（因果后继关系）
      · `phase_compat`：若 `α ≺ β` 且 `β = α∘γ`，则 `actionPhase γ ≠ 0`
        （因果后继必然伴随非平凡相位跃迁）

    这是 V1 A3（因果偏序）+ A4（作用量 e^{iS}）在 v23 语言中的最小
    独立层翻译。 -/
structure V1CausalAmplitudeLayer {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C] where
  /-- 因果序关系 -/
  causalOrder : C → C → Prop
  /-- 反自反性 -/
  irrefl : ∀ x : C, ¬ causalOrder x x
  /-- 传递性 -/
  trans : ∀ x y z : C, causalOrder x y → causalOrder y z → causalOrder x z
  /-- 与组合相容：α ≺ α∘β -/
  compat : ∀ α β : C, causalOrder α (A.compose α β)
  /-- 因果-相位相容：若 α ≺ β 且 β = α∘γ，则 actionPhase γ ≠ 0 -/
  phase_compat : ∀ α β γ : C,
    β = A.compose α γ → causalOrder α β →
    (@actionPhase M C A Cx γ) ≠ (0 : Real.Angle)

/-! ============================================================================
    §2. 关键引理：无右单位元 ⇒ 不存在相位为 0 的非平凡操作

    若存在 γ 使 actionPhase γ = 0，则 amplitude γ = 1，
    从而对任意 α，amplitude(α∘γ) = amplitude α * 1 = amplitude α，
    由 amplitude_injective 得 α∘γ = α，即 γ 是右单位元。
    因此在无右单位元的模型上，所有 γ 的相位都不为 0。
   ============================================================================ -/

/-- **相位零 ⇒ 右单位元**（W1 严格）：
    若 `actionPhase γ = 0`，则对任意 α，`A.compose α γ = α`。

    证明链：
      actionPhase γ = 0
        ⇒ toCircle(actionPhase γ) = 1
        ⇒ amplitude γ = 1          [actionPhase_reconstructs_amplitude]
        ⇒ amplitude(α∘γ) = amplitude α * 1 = amplitude α   [comp_rule]
        ⇒ α∘γ = α                 [amplitude_injective] -/
theorem phase_zero_implies_right_id {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (γ : C) (h : (@actionPhase M C A Cx γ) = (0 : Real.Angle)) :
    ∀ α : C, A.compose α γ = α := by
  have h_amp_one : Cx.amplitude γ = 1 := by
    have h_rec : (Real.Angle.toCircle (@actionPhase M C A Cx γ) : ℂ) = Cx.amplitude γ :=
      @actionPhase_reconstructs_amplitude M C A Cx γ
    rw [h] at h_rec
    simpa using h_rec.symm
  intro α
  have h_comp : Cx.amplitude (A.compose α γ) = Cx.amplitude α := by
    rw [Cx.comp_rule α γ, h_amp_one, mul_one]
  exact Cx.amplitude_injective h_comp

/-- **无右单位元 ⇒ 所有相位非零**（W1 严格）：
    若模型无右单位元（`∀ x y, x∘y ≠ x`），则对任意 γ，`actionPhase γ ≠ 0`。

    这是 §1 `phase_compat` 字段在无右单位元模型上成立的核心依据。 -/
theorem no_right_id_implies_all_phases_nonzero {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (h_no_id : ∀ x y : C, A.compose x y ≠ x) (γ : C) :
    (@actionPhase M C A Cx γ) ≠ (0 : Real.Angle) := by
  intro h_zero
  have h_right_id : ∀ α : C, A.compose α γ = α := phase_zero_implies_right_id γ h_zero
  have h_contra : A.compose γ γ = γ := h_right_id γ
  exact h_no_id γ γ h_contra

/-! ============================================================================
    §3. 可构造性定理：无右单位元模型上层存在

    取 G1 的条件序 `α ≺ β := ∃ γ, β = α∘γ ∧ β ≠ α`。
    由 OrderAndFixedPoint.conditional_order，它是严格偏序且与 compose 相容。
    由 §2 引理，`phase_compat` 成立。
    因此 `V1CausalAmplitudeLayer` 在无右单位元模型类上可构造。
   ============================================================================ -/

/-- **可构造性定理（W2，模型类假设）**：
    在无右单位元的 `AxiomA` + `AxiomC` 模型上，存在 V1 因果-振幅层。

    构造：
      causalOrder α β := ∃ γ, β = α∘γ ∧ β ≠ α
    验证：
      · 严格偏序 + 相容：OrderAndFixedPoint.conditional_order
      · phase_compat：若 β = α∘γ 且 α ≺ β，则 β ≠ α ⇒ γ 不是右单位元
        （否则 β = α），由 no_right_id_implies_all_phases_nonzero 得
        actionPhase γ ≠ 0。 -/
theorem layer_constructible_on_no_right_id {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (h_no_id : ∀ x y : C, A.compose x y ≠ x) :
    Nonempty (V1CausalAmplitudeLayer (M := M) (C := C)) := by
  let CA : CompilerAxiom M C := {
    compose := A.compose,
    assoc := A.compose_assoc,
    input := A.input,
    compose_input := A.compose_input,
    input_nodup := A.input_nodup
  }
  let r : C → C → Prop := fun x y => ∃ z : C, y = A.compose x z ∧ y ≠ x
  have h_order : CompatibleStrictOrder CA r := @conditional_order M C CA h_no_id
  refine ⟨{
    causalOrder := r,
    irrefl := h_order.irrefl,
    trans := h_order.trans,
    compat := h_order.compat,
    phase_compat := by
      intro α β γ h_comp h_causal
      have h_ne : β ≠ α := by
        rcases h_causal with ⟨_, _, hne⟩
        exact hne
      intro h_zero
      have h_eq : A.compose α γ = α := phase_zero_implies_right_id γ h_zero α
      have h_beta_eq_alpha : β = α := by
        rw [h_comp]
        exact h_eq
      exact h_ne h_beta_eq_alpha
  }⟩

/-! ============================================================================
    §4. 不可均匀构造（no-go）

    关键观察：若模型存在 α 使 `compose α α = α`（幂等元），则层的
    `compat α α` 给出 `causalOrder α (compose α α) = causalOrder α α`，
    与 `irrefl α` 矛盾。因此任何含幂等元的模型都不存在层。

    退化模型（M = C = Unit，compose 恒等）满足此条件，且满足 AxiomA + AxiomC。
    故不存在对所有模型都成立的均匀构造——见 `no_layer_on_trivial`。
   ============================================================================ -/

/-- **含幂等元的模型上不存在层（W1 严格）**：
    若 `∃ α, compose α α = α`，则 `compat` 与 `irrefl` 直接矛盾。 -/
theorem no_layer_when_idempotent {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (h : ∃ α : C, A.compose α α = α) :
    V1CausalAmplitudeLayer (M := M) (C := C) → False := by
  intro layer
  rcases h with ⟨α, hα⟩
  have h_compat : layer.causalOrder α (A.compose α α) := layer.compat α α
  rw [hα] at h_compat
  exact layer.irrefl α h_compat

/-- **退化模型 AxiomA**（全局 instance）：M = C = Unit，compose/output 恒为 `()`。
    所有字段平凡成立；`compose () () = ()`，故含幂等元。 -/
instance trivialAxiomA : AxiomA Unit Unit where
  input := fun _ => []
  output := fun _ => ()
  input_nodup := by simp
  compose := fun _ _ => ()
  compose_input := by simp
  compose_output := by simp
  compose_assoc := by simp

/-- **退化模型 AxiomC**（全局 instance）：amplitude 恒为 1。
    norm_one = normSq(1) = 1；comp_rule = 1·1 = 1；injective 在单元素上平凡。 -/
instance trivialAxiomC : AxiomC Unit Unit where
  amplitude := fun _ => 1
  norm_one := by
    intro _
    simp
  comp_rule := by
    intro _ _
    simp
  amplitude_injective := by
    intro _ _ _
    rfl

/-- **退化模型上不存在层（W1 严格）**：
    退化模型 (Unit) 含幂等元 `compose () () = ()`，故不存在层。
    这直接蕴含：任何声称对所有模型都给出层的均匀构造，在退化模型上失效。 -/
theorem no_layer_on_trivial :
    Nonempty (V1CausalAmplitudeLayer (M := Unit) (C := Unit)) → False := by
  intro h_exists
  rcases h_exists with ⟨layer⟩
  exact no_layer_when_idempotent (M := Unit) (C := Unit) ⟨(), rfl⟩ layer

/-! ============================================================================
    §5. 判定登记（四档）

    对用户问题 #2「V1 的因果性与振幅层能否作为独立结构层架在 v23 之上」：

      振幅层 S                  : A —— 由 AxiomC 导出（G4，零新增公设）
      因果偏序（与 compose 相容）: B —— 不可均匀导出（G1 no-go）；
                                      无右单位元模型上可构造（条件定理）
      二者组合为独立层          : B —— 无右单位元模型类上可构造且
                                      因果-相位相容定理成立（§2/§3）；
                                      不可均匀构造（§4）

    不属 C 档：因为不需要新增公设——层的全部字段都从 AxiomA+AxiomC
    的现有结构构造（序来自 compose 的可达性，相位来自 amplitude）。
    不属 A 档：因为不能对所有模型均匀构造。

    Fin 7 见证：Enhanced 的 fin7Model 中 output=id、amplitude=7 次单位根、
    标准因果序同时非平凡（CSQIT_Enhanced.Bridge.fin7_opweaving_nonvacuous），
    说明因果性与振幅在具体模型中可以共存——但该序是 AxiomB' 外加字段，
    不是从 AxiomA+AxiomC 导出的。这佐证了「层可架上去，但不是自动导出」。
   ============================================================================ -/

end CSQIT_V1Bridge
