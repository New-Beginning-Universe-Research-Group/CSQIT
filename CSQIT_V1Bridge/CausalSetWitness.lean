/-
================================================================================
CSQIT_V1Bridge — 见证模型的因果集公理（G16）
模块: CSQIT_V1Bridge.CausalSetWitness
版本: v0.1.0（2026-11-07）
================================================================================

承接 `StructuralLimits`（G12–G15）。本模块把 G8 的见证模型
（`C = ℕ`, `compose a b = a + b + 1`, `amplitude n = exp(i(n+1)·π√2)`）
的可达因果序提升为一个**真正的因果集**（V1/V7 D2.2、T2.1 的
局部有限严格偏序片段）：

  · G16a（A 档）：可达序 `α ≺ β` 在见证模型上恰好是自然数严格序 `α < β`；
  · G16b（A 档）：该序无环、传递、局部有限（每个区间 `[α, β]` 有限）；
  · G16c（A 档）：该序是全序（链），即见证模型给出一个**线性时间**；
  · G16d（A 档）：该序与 `compose` 相容，且无极大元（时间无终点）。

这回答了「v23 能否承载因果集」的一半：至少存在一个非空洞、
非有限、振幅非平凡的合法 v23 模型，其派生因果序满足因果集的
局部有限性要求。另一半——「是否每个模型都给出线性时间」——
由 `NonTotalModel` 以乘积模型否定（若该模块成立）；
若未成立，则登记为未解决，不用措辞绕过。

纪律：零新增 axiom、零 sorry；不修改既有文件。
================================================================================ -/

import CSQIT_V1Bridge.LayerWitness
import CSQIT_V1Bridge.StructuralLimits

namespace CSQIT_V1Bridge

open CSQIT_W1.CompilerAxioms
open CSQIT_W1.Foundation

/-! ============================================================================
    §1. 一般定义：局部有限因果集
   ============================================================================ -/

/-- **局部有限因果集**（V1/V7 D2.2 的严格序片段）：
    无环、传递，且每个「区间」`{z | x ≺ z ∧ z ≺ y}` 有限。 -/
structure LocallyFiniteCausalSet (α : Type*) (r : α → α → Prop) : Prop where
  /-- 无自环 -/
  irrefl : ∀ a : α, ¬ r a a
  /-- 传递 -/
  trans : ∀ a b c : α, r a b → r b c → r a c
  /-- 局部有限 -/
  locallyFinite : ∀ a b : α, {z : α | r a z ∧ r z b}.Finite

/-! ============================================================================
    §2. G16a：见证模型的可达序 = 自然数严格序
   ============================================================================ -/

/-- 见证模型上的可达关系：`a ≺ b` 当且仅当存在 γ 使 `b = a ∘ γ` 且不相等。 -/
def witnessReach (a b : ℕ) : Prop :=
  ∃ γ : ℕ, b = witnessAxiomA.compose a γ ∧ b ≠ a

/-- **G16a（W1，A 档）**：在见证模型上，可达关系恰为自然数严格序。 -/
theorem witnessReach_iff_lt (a b : ℕ) : witnessReach a b ↔ a < b := by
  constructor
  · rintro ⟨γ, hb, _⟩
    unfold witnessAxiomA at hb
    simp only [AxiomA.compose] at hb
    omega
  · intro h
    refine ⟨b - a - 1, ?_, ?_⟩
    · unfold witnessAxiomA
      simp only [AxiomA.compose]
      omega
    · omega

/-! ============================================================================
    §3. G16b–d：因果集公理与链性质
   ============================================================================ -/

/-- **G16b-1（W1，A 档）**：可达序无自环。 -/
theorem witnessReach_irrefl (a : ℕ) : ¬ witnessReach a a := by
  rw [witnessReach_iff_lt]
  omega

/-- **G16b-2（W1，A 档）**：可达序传递。 -/
theorem witnessReach_trans {a b c : ℕ} (hab : witnessReach a b) (hbc : witnessReach b c) :
    witnessReach a c := by
  rw [witnessReach_iff_lt] at hab hbc ⊢
  omega

/-- **G16b-3（W1，A 档）**：每个区间有限。 -/
theorem witnessReach_interval_finite (a b : ℕ) :
    {z : ℕ | witnessReach a z ∧ witnessReach z b}.Finite := by
  refine (Finset.Icc a b).finite_toSet.subset ?_
  intro z hz
  simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_Icc] at hz ⊢
  obtain ⟨h1, h2⟩ := hz
  rw [witnessReach_iff_lt] at h1 h2
  omega

/-- **G16b（W1，A 档）**：见证模型的可达序是一个局部有限因果集。 -/
theorem witness_is_locallyFiniteCausalSet :
    LocallyFiniteCausalSet ℕ witnessReach where
  irrefl := witnessReach_irrefl
  trans := fun _ _ _ => witnessReach_trans
  locallyFinite := witnessReach_interval_finite

/-- **G16c（W1，A 档）**：可达序是全序（链）——见证模型给出一条线性时间。 -/
theorem witnessReach_total (a b : ℕ) (h : a ≠ b) :
    witnessReach a b ∨ witnessReach b a := by
  rw [witnessReach_iff_lt, witnessReach_iff_lt]
  omega

/-- **G16d-1（W1，A 档）**：可达序与 `compose` 相容。 -/
theorem witnessReach_compatible (a b : ℕ) :
    witnessReach a (witnessAxiomA.compose a b) := by
  refine ⟨b, ?_, ?_⟩
  · rfl
  · unfold witnessAxiomA
    simp only [AxiomA.compose]
    omega

/-- **G16d-2（W1，A 档）**：可达序无极大元——每个事件都有后继。 -/
theorem witnessReach_no_maximal (a : ℕ) : ∃ b : ℕ, witnessReach a b :=
  ⟨a + 1, by rw [witnessReach_iff_lt]; omega⟩

end CSQIT_V1Bridge
