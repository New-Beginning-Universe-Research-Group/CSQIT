/-
CSQIT — 时间箭头（因果序就是时间）
文件: DerivedLaws/Spacetime/TimeArrow.lean
版本: v11.2.4
日期: 2026-07-19
编译状态: ⏸ 未参与编译（未在 lakefile.lean 中注册）

================================================================================
定律名称：时间箭头（过去≠未来的方向性）
================================================================================

物理中的对应：
  时间有方向——过去和未来是不同的。
  这体现在：
  - 热力学第二定律（熵增）
  - 因果律（原因先于结果）
  - 记忆（我们记得过去，不是未来）
  - 辐射（波从源向外扩散，不是向内汇聚）

  但在基础物理定律中（牛顿力学、相对论、量子力学），
  时间似乎是对称的——定律在时间反演下不变。
  这就是"时间箭头之谜"：为什么对称的定律会产生不对称的世界？

CSQIT 中的对应：
  时间不是一个独立的维度，而是因果序本身。
  因果序天然有方向（≤ 是偏序，不是对称的），
  因此时间箭头不是"涌现"出来的，
  而是从最基础的层面就内置在结构中。

依赖层级：🟢 W2 条件性定理
  数学核心（因果序有方向）：🔵 W1 严格（偏序定义的平凡推论）
  物理对应（= 时间箭头）：🟢 W2 条件性（需要"因果序 = 时间"假设）

物理意义：
  时间箭头之谜在 CSQIT 中自动消解——
  时间本来就是有方向的，因为因果本来就是有方向的。
  物理定律的"时间反演对称性"是宏观近似，
  而不是基础层面的性质。

适用范围：
  - 适用于所有因果格
  - 时间箭头 = 因果序的方向
  - 过去 = 因果过去集合（causalPast）
  - 未来 = 因果未来集合（causalFuture）
================================================================================
-/

import Core.W1.CausalLattice

namespace CSQIT.DerivedLaws.Spacetime

open CausalLattice

variable {M : Type*} [CausalLattice M]

/--
时间的定义：时间 = 因果序

在 CSQIT 中，时间不是一个独立的舞台，
而是事件之间的因果关系结构本身。

x ≤ y 的物理意义就是：
  x 在时间上先于 y，
  x 是 y 的因果过去的一部分。
-/
theorem time_is_causal_order (x y : M) :
    (x ≤ y) ↔ (x 在时间上先于 y) := by
  -- 这是定义性的——时间就是因果序
  constructor
  · intro h
    exact h
  · intro h
    exact h

/--
时间箭头定理：因果关系是不对称的（除非 x = y）。

如果 x < y（严格先于），那么不可能有 y < x。
这就是时间箭头的最纯粹表达——
过去和未来是不对称的。
-/
theorem time_arrow_asymmetric {x y : M} (h : x < y) :
    ¬ (y < x) := by
  intro h'
  have h1 : x ≤ y := le_of_lt h
  have h2 : y ≤ x := le_of_lt h'
  have h3 : x = y := le_antisymm h1 h2
  have h4 : ¬ (x < y) := by
    rw [h3]
    <;> simp
  exact h4 h

/--
因果过去的下闭性：
  如果 x ≤ y，那么 x 的因果过去是 y 的因果过去的子集。

这意味着：当你"向未来前进"时，你的因果历史只会增加，不会减少。
这是热力学时间箭头（熵增）的基础。
-/
theorem causalPast_grows_with_time {x y : M} (h : x ≤ y) :
    causalPast x ⊆ causalPast y :=
  causalPast_downward_closed h

/--
因果未来的上闭性：
  如果 x ≤ y，那么 y 的因果未来是 x 的因果未来的子集。

向未来前进，你的"可能的未来"在缩小——
过去是确定的，未来是开放的（在分支的意义上）。
-/
theorem causalFuture_shrinks_with_time {x y : M} (h : x ≤ y) :
    causalFuture y ⊆ causalFuture x := by
  intro z hz
  have h1 : y ≤ z := hz
  have h2 : x ≤ z := le_trans h h1
  exact h2

/--
时间的不对称性总结：
  过去是下闭的，未来是上闭的。
  过去随时间增长，未来随时间缩小。

这就是时间箭头的全部内容——
它不是神秘的涌现性质，
而是因果偏序的基本特征。
-/
theorem time_asymmetry_summary {x y : M} (h : x < y) :
    (causalPast x ⊂ causalPast y) ∧ (causalFuture y ⊂ causalFuture x) := by
  have h1 : causalPast x ⊆ causalPast y := causalPast_grows_with_time (le_of_lt h)
  have h2 : causalFuture y ⊆ causalFuture x := causalFuture_shrinks_with_time (le_of_lt h)
  have h3 : y ∉ causalPast x := by
    intro hy
    have h4 : y ≤ x := hy
    have h5 : ¬ (x < y) := by
      have h6 : y ≤ x := h4
      have h7 : ¬ (x < y) := by
        intro h8
        have h9 : x ≤ y := le_of_lt h8
        have h10 : x = y := le_antisymm h9 h6
        rw [h10] at h8
        <;> simp at h8
      exact h7
    exact h5 h
  have h4 : y ∈ causalPast y := by
    exact le_refl y
  have h5 : causalPast x ⊂ causalPast y := by
    refine ⟨h1, ?_⟩
    intro h6
    have h7 : y ∈ causalPast x := h6 h4
    exact h3 h7
  have h6 : x ∉ causalFuture y := by
    intro hx
    have h7 : y ≤ x := hx
    have h8 : ¬ (x < y) := by
      have h9 : y ≤ x := h7
      have h10 : ¬ (x < y) := by
        intro h11
        have h12 : x ≤ y := le_of_lt h11
        have h13 : x = y := le_antisymm h12 h9
        rw [h13] at h11
        <;> simp at h11
      exact h10
    exact h8 h
  have h7 : x ∈ causalFuture x := by
    exact le_refl x
  have h8 : causalFuture y ⊂ causalFuture x := by
    refine ⟨h2, ?_⟩
    intro h9
    have h10 : x ∈ causalFuture y := h9 h7
    exact h6 h10
  exact ⟨h5, h8⟩

end CSQIT.DerivedLaws.Spacetime
