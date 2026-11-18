/-
================================================================================
CSQIT_WeaveBridge.Independence
第二步判定的形式化落码：`Weave` 相对 `AxiomA` 是**独立**的。

两条可机检事实：
  I1  `CausalSite.idx : Nat` 不由 `out : M`（M 侧唯一可观测数据）决定；
      反例模型对：`out` 同为 `()`，`idx` 为 0 与 1。
  I2  端点固定后 `path` 仍不唯一（自环路径合法，因 `causalIncomparable s s`
      由归档 L51-52 恒真）。

第三步：`input ≡ []` 与 `Weave` 的存在性并存 —— `Weave` 五字段无一处引用
`input`。本文件用"任意输入函数 + 恒空前提"的形式把这一点写成定理。

零新增 axiom、零 sorry；不 import Mathlib（原因见 WeaveCore.lean 文件头）。
================================================================================ -/
import CSQIT_WeaveBridge.WeaveCore

namespace CSQIT_WeaveBridge

universe u

/-! ============================================================================
   §1. 独立性 I1：位点索引不由输出关系元决定
   ============================================================================ -/

/-- **I1（否定式定理）**：不存在只依赖 `out` 的函数能算出 `idx`。

    模型对：`M = Unit`；位点 `⟨0, ()⟩` 与 `⟨1, ()⟩` 的 `out` 是同一项 `()`，
    `idx` 不同。`AxiomA` 侧（`M = Unit`、`C = Unit`，`compose` 只能取常函数）
    在两侧完全相同，故 `compose` 逐字相同而 `Weave` 的站点不同。 -/
theorem site_idx_not_determined_by_out :
    ¬ ∃ f : Unit → Nat, ∀ s : CausalSite Unit, s.idx = f s.out := by
  rintro ⟨f, hf⟩
  have h0 : (0 : Nat) = f () := hf ⟨0, ()⟩
  have h1 : (1 : Nat) = f () := hf ⟨1, ()⟩
  have h01 : (0 : Nat) = 1 := by rw [h0, ← h1]
  exact absurd h01 (by decide)

/-- **模型对**：`out` 逐字相同、`idx` 不同的两个位点。 -/
theorem distinct_sites_same_out :
    (⟨0, ()⟩ : CausalSite Unit) ≠ ⟨1, ()⟩
    ∧ (⟨0, ()⟩ : CausalSite Unit).out = (⟨1, ()⟩ : CausalSite Unit).out := by
  constructor
  · intro h
    have h01 : (0 : Nat) = 1 := congrArg CausalSite.idx h
    exact absurd h01 (by decide)
  · rfl

/-! ============================================================================
   §2. 独立性 I2：端点固定后 `path` 仍不唯一
   ============================================================================ -/

/-- 自环路径 `[s, s]`：由 `causalIncomparable s s` 恒真而合法（归档 L51-52）。 -/
def loop2 {M : Type u} (s : CausalSite M) : Weave s s where
  path := [s, s]
  path_nonempty := by simp
  head_eq := rfl
  last_eq := by simp
  causal_chain := by
    intro i hi
    right
    have hle : i + 1 ≤ 1 := Nat.lt_succ_iff.mp hi
    have hle0 : i ≤ 0 := Nat.le_of_succ_le_succ hle
    have hi0 : i = 0 := Nat.le_zero.mp hle0
    subst hi0
    refine ⟨?_, ?_⟩
    · simp [causalLT]
    · simp [causalLT]

/-- **I2**：同端点上的两个 `Weave` 路径不同，故 `Weave L R` 不是单点类型。 -/
theorem weave_fiber_nontrivial :
    ∃ w₁ w₂ : Weave ((⟨0, ()⟩ : CausalSite Unit)) ⟨0, ()⟩, w₁.path ≠ w₂.path := by
  refine ⟨Weave.trivial ⟨0, ()⟩, loop2 ⟨0, ()⟩, ?_⟩
  show ([⟨0, ()⟩] : List (CausalSite Unit)) ≠ [⟨0, ()⟩, ⟨0, ()⟩]
  intro h
  cases h

/-! ============================================================================
   §3. 与 core_collapse 的关系：并存
   ============================================================================ -/

/-- **并存定理**：任意输入函数下、即使输入恒空，`Weave` 依然存在。

    `input : C → List M` 与 `Weave` 的构造互不相干：`Weave` 五字段
    （`path / path_nonempty / head_eq / last_eq / causal_chain`）没有一处引用
    `input`。故 `input ≡ []` 既不能使它恒真、也不能使它恒假。 -/
theorem input_collapse_and_weave_coexist {M C : Type u}
    (input : C → List M) (h0 : ∀ α, input α = []) (α : C) (s : CausalSite M) :
    input α = [] ∧ Nonempty (Weave s s) :=
  ⟨h0 α, ⟨Weave.trivial s⟩⟩

/-- **对照**：`Weave` 的构造不消费任何公理数据。 -/
def weave_needs_no_axiom_data {M : Type u} (s : CausalSite M) : Weave s s :=
  Weave.trivial s

end CSQIT_WeaveBridge
