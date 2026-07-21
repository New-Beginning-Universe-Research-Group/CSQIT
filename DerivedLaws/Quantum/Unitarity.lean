/-
CSQIT — 振幅幺正性（量子力学幺正性的代数起源）
文件: DerivedLaws/Quantum/Unitarity.lean
版本: v11.2.4
日期: 2026-07-19
编译状态: ⏸ 未参与编译（未在 lakefile.lean 中注册）

================================================================================
定律名称：量子幺正性（概率守恒）
================================================================================

物理中的对应：
  量子力学中，时间演化是幺正的——概率守恒。
  一个封闭系统的所有可能测量结果的概率之和永远等于 1。
  这是量子力学最基本的原理之一。

CSQIT 中的对应：
  每个编织规则的振幅模长平方为 1（|amplitude α|² = 1）。
  振幅的复合保持模长（复合的模 = 模的乘积 = 1×1 = 1）。
  这就是幺正性的代数本质。

依赖层级：🟢 W2 条件性定理
  数学核心（振幅模长平方 = 1）：🔵 W1 严格（从 AxiomC.norm_one 直接导出）
  物理对应（= 概率守恒/量子幺正性）：🟢 W2 条件性（需要"|振幅|² = 概率"假设）

物理意义：
  概率守恒不是一个额外的"自然定律"，
  而是编织振幅结构的直接结果。
  只要基本规则的振幅模长为 1，
  任何复合过程的概率自然守恒。

适用范围：
  - 适用于所有满足 AxiomA + AxiomC 的理论
  - 幺正性是振幅层面的精确性质
  - 在宏观极限下，表现为概率守恒
================================================================================
-/

import Core.W1.AmplitudeTheorems

namespace CSQIT.DerivedLaws.Quantum

variable {M C : Type*} [AxiomA M C] [AxiomC M C]

/--
振幅幺正性定理：
  每个基本规则的振幅模长平方 = 1。

  |amplitude α|² = 1

这是量子力学幺正性的最基本形式——
每个基本过程都是"概率保持"的。
-/
theorem amplitude_unitarity (α : C) :
    Complex.normSq (AxiomC.amplitude α) = 1 :=
  AxiomC.norm_one α

/--
复合格式的幺正性：
  两个规则复合后的振幅模长 = 模长的乘积 = 1 × 1 = 1。

  |amplitude (α ∘ β)| = |amplitude α| × |amplitude β| = 1

这保证了任意复合过程仍然是幺正的——
概率守恒在任意复杂过程中都成立。
-/
theorem compose_preserves_unitarity (α β : C) :
    Complex.normSq (AxiomC.amplitude (AxiomA.compose α β)) = 1 := by
  have h1 : Complex.normSq (AxiomC.amplitude (AxiomA.compose α β)) =
           Complex.normSq (AxiomC.amplitude α * AxiomC.amplitude β) := by
    rw [amplitude_compose α β]
  rw [h1]
  rw [Complex.normSq_mul]
  rw [amplitude_unitarity α, amplitude_unitarity β]
  <;> ring

/--
振幅实部的界：
  -1 ≤ Re(amplitude α) ≤ 1

这意味着概率振幅的"经典分量"被限制在 [-1, 1] 之间。
-/
theorem amplitude_re_bounded (α : C) :
    |(AxiomC.amplitude α).re| ≤ 1 :=
  amplitude_re_le_one α

/--
振幅虚部的界：
  -1 ≤ Im(amplitude α) ≤ 1

虚部同样被限制在 [-1, 1] 之间。
-/
theorem amplitude_im_bounded (α : C) :
    |(AxiomC.amplitude α).im| ≤ 1 :=
  amplitude_im_le_one α

/--
共轭振幅的幺正性：
  振幅的共轭同样满足模长平方为 1。

  |conj(amplitude α)|² = 1

这是时间反演对称性的代数版本——
反转过程的振幅是原过程振幅的共轭，
同样满足幺正性。
-/
theorem conjugate_unitarity (α : C) :
    Complex.normSq (conj (AxiomC.amplitude α)) = 1 :=
  amplitude_conj_normSq α

/--
幺正性的物理诠释：概率守恒。

如果我们将 |amplitude α|² 诠释为过程 α 的概率，
那么幺正性就是概率守恒的代数表达。

注意：这一步是 W2/W3 层的诠释，不是 W1 层的定理。
W1 层只保证模长平方为 1，
而"模长平方 = 概率"是额外的物理对应。
-/
/- 猜想：probability_conservation_interpretation 内容：|amplitude α|² 可以诠释为过程 α 的概率（由振幅模长平方为1推出） 状态：🟢 W2 条件性 -/

end CSQIT.DerivedLaws.Quantum
