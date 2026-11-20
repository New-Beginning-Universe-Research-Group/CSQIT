/-
================================================================================
CSQIT_V1Bridge — 第二十一轮：因果层可以脱离振幅层独立存在（G37）
模块: CSQIT_V1Bridge.LayerIndependence
版本: v0.1.0（2026-11-08）
================================================================================

动机：用户问题 (ii)「V1 的因果性与振幅层能否作为独立结构层架在 v23 之上」
此前只有一侧见证——G33（`FiniteSeparation`）证明有限 `Bool` 模型可带
振幅层而无因果层。本模块补上**另一侧**：构造一个纯 `AxiomA` 模型

  `C = {非空 Bool 列表}`，`compose = 拼接`

它非交换、可消去、**无右作用元**，因此按 G34-pre / G34a：
  · 存在相容严格偏序（因果层存在）；
  · 但 `AxiomC` 空间为空（振幅层不存在）——
    因为 `AxiomC` 会强迫 compose 交换（见下方 `neList_no_axiomC`）。

结论（G37，A 档）：
  因果结构与振幅结构在 v23 上**逻辑独立**：
  · 振幅层可以单独存在（G33 的 `Bool`，有限、有单位元、无因果层）；
  · 因果层可以单独存在（本模块的非空列表模型，无振幅层）；
  · 两者同时存在时受 G35c-2 限制（有限载体不可能）。

纪律：零新增 axiom、零 sorry；不修改 CSQIT_W1 / CSQIT_Enhanced 与既有
V1Bridge 文件；只新增本文件与 lakefile 一行 root。
依赖：CSQIT_W1.Foundation、CSQIT_V1Bridge.OrderUniqueness（G34）。
================================================================================ -/

import CSQIT_W1.Foundation
import CSQIT_V1Bridge.OrderUniqueness

namespace CSQIT_V1Bridge

open CSQIT_W1.Foundation

/-- 载体：非空 `Bool` 列表。去掉空表是为了让「拼接」没有右单位元。 -/
def NeList : Type := { l : List Bool // l ≠ [] }

/-- 拼接（非空性由长度论证保持）。 -/
def neAppend (a b : NeList) : NeList :=
  ⟨a.val ++ b.val, by
    intro h
    have hlen : (a.val ++ b.val).length = 0 := by
      simpa using congrArg List.length h
    rw [List.length_append] at hlen
    have ha0 : a.val.length = 0 := by omega
    exact a.2 (List.eq_nil_of_length_eq_zero ha0)⟩

/-- **G37a（A 档）**：拼接没有右作用元。
    若 `x ++ y = x`，取长度得 `x.length + y.length = x.length`，故
    `y = []`，与 `y` 的非空性矛盾。 -/
theorem neList_no_right_id : ∀ x y : NeList, neAppend x y ≠ x := by
  intro x y h
  have h' : x.val ++ y.val = x.val := congrArg Subtype.val h
  have hlen : x.val.length + y.val.length = x.val.length := by
    simpa using congrArg List.length h'
  have hy0 : y.val.length = 0 := by omega
  exact y.2 (List.eq_nil_of_length_eq_zero hy0)

/-- 非空列表拼接构成 `AxiomA` 模型（输入恒空、输出恒 `()`）。 -/
instance neListAxiomA : AxiomA Unit NeList where
  input := fun _ => []
  output := fun _ => ()
  input_nodup := by intro α; exact List.nodup_nil
  compose := neAppend
  compose_input := by intro α β; rfl
  compose_output := by intro α β; rfl
  compose_assoc := by
    intro α β γ
    exact Subtype.ext (List.append_assoc α.val β.val γ.val)

/-- **G37b（A 档）**：该模型的 `AxiomC` 空间为空。

    机制：`AxiomC` 的单射乘法振幅迫使
    `amp (a∘b) = amp a * amp b = amp b * amp a = amp (b∘a)`，
    再由单射得 `a∘b = b∘a`（交换性）。取单元素列表 `[true]`、`[false]`，
    拼接次序不同，矛盾。**这正是 `amplitude` 作为到单位圆的同态所携带
    的交换性约束反传到非交换模型的结果。** -/
theorem neList_no_axiomC : ¬ Nonempty (AxiomC Unit NeList) := by
  rintro ⟨Cx⟩
  have hcomm : ∀ a b : NeList, neAppend a b = neAppend b a := by
    intro a b
    apply Cx.amplitude_injective
    change Cx.amplitude (neListAxiomA.compose a b) = Cx.amplitude (neListAxiomA.compose b a)
    rw [Cx.comp_rule, Cx.comp_rule, mul_comm]
  let a : NeList := ⟨[true], by simp⟩
  let b : NeList := ⟨[false], by simp⟩
  have hv : (neAppend a b).val = (neAppend b a).val := congrArg Subtype.val (hcomm a b)
  have hv' : ([true] : List Bool) ++ [false] = [false] ++ [true] := hv
  exact absurd hv' (by decide)

/-- **G37（A 档，主结论）**：存在「只有因果层、没有振幅层」的 v23 模型。
    · `AxiomC` 空间为空；
    · 存在与 `compose` 相容的严格偏序（反自反 + 传递 + 相容）。 -/
theorem neList_causal_without_amplitude :
    (¬ Nonempty (AxiomC Unit NeList)) ∧
    (∃ r : NeList → NeList → Prop,
        (∀ x : NeList, ¬ r x x) ∧
        (∀ x y z : NeList, r x y → r y z → r x z) ∧
        (∀ α β : NeList, r α (neAppend α β))) := by
  refine ⟨neList_no_axiomC, ?_⟩
  exact (exists_compatible_order_iff_no_right_id neListAxiomA).mpr neList_no_right_id

end CSQIT_V1Bridge
