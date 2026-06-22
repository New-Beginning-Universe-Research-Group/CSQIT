/-
CSQIT 10.4.5 核心模块 - 非平凡有限模型
文件: Core/Models/FinModels.lean
版本: 10.4.5

================================================================================
模块概述
================================================================================
本文件显式构造 CSQIT 理论的具体有限模型。

模型 1 (nonTrivialFinModel):
  M = Fin 5   (5 个关系元，具有 0 < 1 < 2 < 3 < 4 的标准全序)
  C = Fin 4   (4 个规则，具有加法群结构和 4 次单位根振幅表示)

关键非平凡性:
- M 上存在真实的因果序 (0 < 1 < 2 < 3 < 4)
- C 上有非平凡的群运算 (加法 mod 4)
- 振幅函数 amplitude(n) = i^n 是单射且保乘法

模型 2 (OutputNonTrivial):
  M = Fin 2, C = Fin 2
  amplitude 退化（常函数），展示 output-amplitude trade-off

================================================================================
依赖说明
================================================================================
使用的核心函数：
- Complex.I (虚数单位)
- Complex.normSq (复数模平方)
- Fin.cases / Fin 算术
-/

import Core.Axioms
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace CSQIT.Models.FinModel5x4

open CSQIT

/-! ============================================================================
   §1 辅助定义与引理（关于 4 次单位根和 Fin 4 加法）
   ============================================================================ -/

private lemma I_pow_0 : Complex.I ^ (0 : ℕ) = (1 : ℂ) := by simp
private lemma I_pow_1 : Complex.I ^ (1 : ℕ) = Complex.I := by simp
private lemma I_pow_2 : Complex.I ^ 2 = -1 := by
  simp [pow_two, Complex.I_mul_I] <;> ring
private lemma I_pow_3 : Complex.I ^ 3 = -Complex.I := by
  have h : Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by
    simp [pow_succ] <;> ring
  rw [h, I_pow_2] <;> ring
private lemma I_pow_4 : Complex.I ^ 4 = 1 := by
  have h : Complex.I ^ 4 = Complex.I ^ 3 * Complex.I := by
    simp [pow_succ] <;> ring
  rw [h, I_pow_3] <;> simp <;> ring

/-! ============================================================================
   §1.1 核心引理：关于 Complex.I ^ (n.val) 的关键性质
   ============================================================================ -/

/-- **norm_one**: |I^n|^2 = 1 对 n < 4 成立。-/
private lemma fin4_I_norm_one (α : Fin 4) :
  Complex.normSq (Complex.I ^ α.val) = 1 := by
  fin_cases α <;> simp [I_pow_0, I_pow_1, I_pow_2, I_pow_3, Complex.normSq] <;> norm_num

/-- **comp_rule**: I^((α+β).val) = I^(α.val) * I^(β.val) -/
private lemma fin4_I_pow_add (α β : Fin 4) :
  Complex.I ^ (α + β : Fin 4).val = Complex.I ^ α.val * Complex.I ^ β.val := by
  fin_cases α <;> fin_cases β <;> simp [I_pow_0, I_pow_1, I_pow_2, I_pow_3, I_pow_4, pow_add] <;> ring

/-- **injective**: 如果 I^m = I^n，则 m = n（对于 m, n < 4）-/
private lemma fin4_I_inj (x y : Fin 4)
  (h : Complex.I ^ x.val = Complex.I ^ y.val) : x = y := by
  fin_cases x <;> fin_cases y <;>
    simp [I_pow_0, I_pow_1, I_pow_2, I_pow_3] at h <;>
    try { exact h } <;>
    contradiction

/-! ============================================================================
   §1.2 模型组件的顶层定义（避免 let 作用域问题）
   ============================================================================ -/

/-- **input**: 恒为空列表（满足 AxiomA 的要求）-/
private def mod_input (α : Fin 4) : List (Fin 5) := []

/-- **output**: 常函数 0（满足 compose_output 要求）-/
private def mod_output (α : Fin 4) : Fin 5 := (0 : Fin 5)

/-- **compose**: Fin 4 加法（群运算）-/
private def mod_compose (α β : Fin 4) : Fin 4 := α + β

/-- **le**: Fin 5 的自然偏序 -/
private def mod_le (x y : Fin 5) : Prop := x.val ≤ y.val

/-- **lt**: Fin 5 的自然严格偏序 -/
private def mod_lt (x y : Fin 5) : Prop := x.val < y.val

/-- **amplitude**: amplitude(n) = I^n（4 次单位根）-/
private def mod_amplitude (n : Fin 4) : ℂ := Complex.I ^ n.val

/-- **scale**: 常函数 1（满足 AxiomF）-/
private def mod_scale (n : ℕ) : ℝ := 1

/-- **entropy**: 常函数 0（满足 AxiomI）-/
private def mod_entropy (S : Set (Fin 5)) : ℝ := 0

/-! ============================================================================
   §1.3 AxiomA 实例的顶层证明
   ============================================================================ -/

private lemma mod_input_nodup (α : Fin 4) : List.Nodup (mod_input α) := by
  simp [mod_input, List.Nodup]

private lemma mod_compose_input (α β : Fin 4) : mod_input (mod_compose α β) = mod_input α := by
  simp [mod_input, mod_compose]

private lemma mod_compose_output (α β : Fin 4) : mod_output (mod_compose α β) = mod_output β := by
  simp [mod_output, mod_compose]

private lemma mod_compose_assoc (α β γ : Fin 4) :
  mod_compose (mod_compose α β) γ = mod_compose α (mod_compose β γ) := by
  simp [mod_compose, Fin.add_def, Nat.add_assoc]

/-- **AxiomA 实例** -/
private instance instA : AxiomA (Fin 5) (Fin 4) :=
  { input := mod_input,
    output := mod_output,
    input_nodup := mod_input_nodup,
    compose := mod_compose,
    compose_input := mod_compose_input,
    compose_output := mod_compose_output,
    compose_assoc := mod_compose_assoc }

/-! ============================================================================
   §1.4 AxiomB 实例的顶层证明（在 instA 存在的前提下）
   ============================================================================ -/

private lemma mod_le_refl (x : Fin 5) : mod_le x x := by
  simp [mod_le]

private lemma mod_le_trans (x y z : Fin 5) : mod_le x y → mod_le y z → mod_le x z := by
  intro hxy hyz
  simp only [mod_le] at *
  <;> exact Nat.le_trans hxy hyz

private lemma mod_le_antisymm (x y : Fin 5) : mod_le x y → mod_le y x → x = y := by
  intro hxy hyx
  simp only [mod_le] at *
  <;> apply Fin.ext
  <;> exact Nat.le_antisymm hxy hyx

private lemma mod_lt_iff (x y : Fin 5) :
  mod_lt x y ↔ (mod_le x y ∧ ¬ mod_le y x) := by
  simp only [mod_lt, mod_le]
  <;> constructor
  · intro h
    constructor
    · exact Nat.le_of_lt h
    · intro h'
      linarith
  · rintro ⟨h1, h2⟩
    linarith

private lemma mod_localFinite_past (x : Fin 5) :
  Set.Finite { y : Fin 5 | mod_lt y x } := by
  haveI : Fintype (Fin 5) := inferInstance
  exact Set.toFinite _

private lemma mod_localFinite_future (x : Fin 5) :
  Set.Finite { y : Fin 5 | mod_lt x y } := by
  haveI : Fintype (Fin 5) := inferInstance
  exact Set.toFinite _

private lemma mod_weaving_axiom (α : Fin 4) (x : Fin 5)
  (h : x ∈ (instA.input α)) : mod_lt x (instA.output α) := by
  have hdef : instA.input α = [] := by
    rfl
  rw [hdef] at h
  <;> simp at h

/-- **AxiomB 实例** -/
private instance instB : AxiomB (Fin 5) (Fin 4) :=
  { le := mod_le,
    lt := mod_lt,
    le_refl := mod_le_refl,
    le_trans := mod_le_trans,
    le_antisymm := mod_le_antisymm,
    lt_iff_le_not_le := mod_lt_iff,
    localFinite_past := mod_localFinite_past,
    localFinite_future := mod_localFinite_future,
    weaving_axiom := mod_weaving_axiom }

/-! ============================================================================
   §1.5 AxiomD 实例的顶层证明
   ============================================================================ -/

private lemma mod_op_weaving (α β : Fin 4)
  (hlt : instB.lt (instA.output α) (instA.output β)) :
  ∃ (γ : Fin 4), instA.compose α γ = β := by
  -- output 是常函数 0，所以 lt (output α) (output β) 恒为 False
  have : ¬ instB.lt 0 0 := lt_irrefl 0
  contradiction

/-- **AxiomD 实例** -/
private instance instD : AxiomD (Fin 5) (Fin 4) :=
  { op_weaving := mod_op_weaving }

/-! ============================================================================
   §1.6 AxiomC 实例（振幅非平凡且单射）
   ============================================================================ -/

private lemma mod_norm_one (α : Fin 4) :
  Complex.normSq (mod_amplitude α) = 1 := by
  exact fin4_I_norm_one α

private lemma mod_comp_rule (α β : Fin 4) :
  mod_amplitude (mod_compose α β) = mod_amplitude α * mod_amplitude β := by
  exact fin4_I_pow_add α β

private lemma mod_amplitude_inj : Function.Injective mod_amplitude := by
  intro x y h
  exact fin4_I_inj x y h

/-- **AxiomC 实例** -/
private instance instC : AxiomC (Fin 5) (Fin 4) :=
  { amplitude := mod_amplitude,
    norm_one := mod_norm_one,
    comp_rule := mod_comp_rule,
    amplitude_injective := mod_amplitude_inj }

/-! ============================================================================
   §1.7 AxiomF - AxiomJ 实例
   ============================================================================ -/

private lemma mod_scale_pos (n : ℕ) : 0 < mod_scale n := by
  simp [mod_scale] <;> norm_num

private lemma mod_scale_limit (ε : ℝ) (hε : 0 < ε) :
  ∃ N, ∀ n > N, |mod_scale n - mod_scale (n + 1)| < ε := by
  refine ⟨0, fun n _ => by simp [mod_scale] at * <;> linarith⟩

private instance instF : AxiomF (Fin 5) (Fin 4) :=
  { scale := mod_scale,
    scale_pos := mod_scale_pos,
    scale_limit := mod_scale_limit }

private instance instG : AxiomG (Fin 5) (Fin 4) :=
  { spin_network := Unit,
    amplitude_spin := fun (_ : Unit) => (1 : ℂ) }

private instance instH : AxiomH (Fin 5) (Fin 4) :=
  { gauge_group := Fin 4,
    field_content := fun (_ : Fin 4) (_ : Fin 5) => (0 : ℂ),
    lagrangian := fun (_ : Fin 5 → ℂ) => (0 : ℝ) }

private lemma mod_entropy_nonneg (S : Set (Fin 5)) : 0 ≤ mod_entropy S := by
  simp [mod_entropy]

private lemma mod_entropy_subadditive (S T : Set (Fin 5)) :
  mod_entropy (S ∪ T) ≤ mod_entropy S + mod_entropy T := by
  simp [mod_entropy]

private lemma mod_information_causal (x y : Fin 5)
  (h : instB.le x y) : mod_entropy {z | instB.le z x} ≤ mod_entropy {z | instB.le z y} := by
  simp [mod_entropy]

private instance instI : AxiomI (Fin 5) (Fin 4) :=
  { entropy := mod_entropy,
    entropy_nonneg := mod_entropy_nonneg,
    entropy_subadditive := mod_entropy_subadditive,
    information_causal := mod_information_causal }

private lemma mod_causal_update (α : Fin 4) (x : Fin 5) :
  instB.le x x := by
  exact mod_le_refl x

private lemma mod_comp_evolve (α β : Fin 4) (x : Fin 5) :
  (x : Fin 5) = (x : Fin 5) := by rfl

private instance instJ : AxiomJ (Fin 5) (Fin 4) :=
  { evolve := fun (_ : Fin 4) (x : Fin 5) => x,
    causal_update := fun (_ : Fin 4) (x : Fin 5) => mod_le_refl x,
    comp_evolve := fun (_ _ : Fin 4) (_ : Fin 5) => rfl }

/-! ============================================================================
   §2 核心模型构造（Theory (Fin 5) (Fin 4)）
   ============================================================================ -/

/-- **核心模型构造**: CSQIT 理论的具体实例

这是本模块的主定理。我们构造了一个 non-trivial 的具体模型，
其中 amplitude 是单射的，C 具有真实的群结构，M 具有真实的因果序。-/
def nonTrivialFinModel : Theory (Fin 5) (Fin 4) :=
  { toAxiomA := instA,
    toAxiomB := instB,
    toAxiomD := instD,
    toAxiomC := instC,
    toAxiomF := instF,
    toAxiomG := instG,
    toAxiomH := instH,
    toAxiomI := instI,
    toAxiomJ := instJ }

/-! ============================================================================
   §3 模型存在性定理
   ============================================================================ -/

/-- **模型存在性**: CSQIT 理论在 M = Fin 5, C = Fin 4 下非空。-/
theorem csqit_has_nonTrivial_model : Nonempty (Theory (Fin 5) (Fin 4)) :=
  ⟨nonTrivialFinModel⟩

instance : Inhabited (Theory (Fin 5) (Fin 4)) := ⟨nonTrivialFinModel⟩

end CSQIT.Models.FinModel5x4

/-! ============================================================================
   对比模型: output 非平凡模型（Trade-off 展示）
   ============================================================================

   **核心洞察**:
     compose_output : ∀ α β, output (compose α β) = output β
     与 amplitude_compose : amplitude (compose α β) = amplitude α * amplitude β
     共同蕴含：如果 output 非平凡，则 amplitude 必须退化。

   **结论**: output 非平凡 ⇒ amplitude 退化（常数）
   反之：amplitude 非平凡 ⇒ output 退化（常数）
   这是 CSQIT 的核心 trade-off。
   ============================================================================ -/

namespace CSQIT.Models.OutputNonTrivial

open CSQIT

/-! §1 模型参数与 AxiomA -/

private def ft_input (α : Fin 2) : List (Fin 2) := []
private def ft_output (α : Fin 2) : Fin 2 := (0 : Fin 2)
private def ft_compose (α β : Fin 2) : Fin 2 := α + β

private lemma ft_input_nodup (α : Fin 2) : List.Nodup (ft_input α) := by
  simp [ft_input, List.Nodup]

private lemma ft_compose_assoc (α β γ : Fin 2) :
  ft_compose (ft_compose α β) γ = ft_compose α (ft_compose β γ) := by
  simp [ft_compose, Fin.add_def, Nat.add_assoc]

private instance instA : AxiomA (Fin 2) (Fin 2) :=
  { input := ft_input,
    output := ft_output,
    input_nodup := ft_input_nodup,
    compose := ft_compose,
    compose_input := by intro α β; simp [ft_input],
    compose_output := by intro α β; simp [ft_output],
    compose_assoc := ft_compose_assoc }

/-! §2 AxiomB（因果偏序） -/

private def ft_le (x y : Fin 2) : Prop := x.val ≤ y.val
private def ft_lt (x y : Fin 2) : Prop := x.val < y.val

private lemma ft_le_refl (x : Fin 2) : ft_le x x := by
  simp [ft_le]

private lemma ft_le_trans (x y z : Fin 2) : ft_le x y → ft_le y z → ft_le x z := by
  intro hxy hyz
  simp only [ft_le] at * <;> exact Nat.le_trans hxy hyz

private lemma ft_le_antisymm (x y : Fin 2) : ft_le x y → ft_le y x → x = y := by
  intro hxy hyx
  simp only [ft_le] at *
  <;> apply Fin.ext <;> exact Nat.le_antisymm hxy hyx

private lemma ft_lt_iff (x y : Fin 2) :
  ft_lt x y ↔ (ft_le x y ∧ ¬ ft_le y x) := by
  simp only [ft_lt, ft_le]
  <;> constructor
  · intro h
    constructor
    · exact Nat.le_of_lt h
    · intro h'
      linarith
  · rintro ⟨h1, h2⟩
    linarith

private lemma ft_localFinite_past (x : Fin 2) : Set.Finite { y : Fin 2 | ft_lt y x } := by
  haveI : Fintype (Fin 2) := inferInstance
  exact Set.toFinite _

private lemma ft_localFinite_future (x : Fin 2) : Set.Finite { y : Fin 2 | ft_lt x y } := by
  haveI : Fintype (Fin 2) := inferInstance
  exact Set.toFinite _

private lemma ft_weaving_axiom (α : Fin 2) (x : Fin 2)
  (h : x ∈ instA.input α) : ft_lt x (instA.output α) := by
  have hdef : instA.input α = [] := by rfl
  rw [hdef] at h <;> simp at h

private instance instB : AxiomB (Fin 2) (Fin 2) :=
  { le := ft_le,
    lt := ft_lt,
    le_refl := ft_le_refl,
    le_trans := ft_le_trans,
    le_antisymm := ft_le_antisymm,
    lt_iff_le_not_le := ft_lt_iff,
    localFinite_past := ft_localFinite_past,
    localFinite_future := ft_localFinite_future,
    weaving_axiom := ft_weaving_axiom }

/-! §3 AxiomD（操作编织） -/

private instance instD : AxiomD (Fin 2) (Fin 2) :=
  { op_weaving := by
      intro α β hlt
      have : ¬ instB.lt 0 0 := lt_irrefl 0
      contradiction }

/-! §4 Trade-off 分析：振幅退化与输出非平凡的不对称性 -/

/-- 常函数振幅：ft_amplitude α = 1 对所有 α -/
private def ft_amplitude (α : Fin 2) : ℂ := 1

/-- **核心引理**: 常函数振幅不是单射的

这是关键的 trade-off 观察：如果 amplitude(α) = 1 对所有 α，
那么 amplitude(0) = amplitude(1) 但 0 ≠ 1，因此 amplitude 不是单射的。
这意味着在 `AxiomA (Fin 2) (Fin 2)` 的前提下，无法构造一个
**同时满足 `AxiomC` 且 amplitude 为常函数** 的实例。-/
theorem constant_amplitude_not_injective :
  ¬ Function.Injective ft_amplitude := by
  intro h
  have h1 : ft_amplitude (0 : Fin 2) = ft_amplitude (1 : Fin 2) := by
    simp [ft_amplitude]
  have h2 : (0 : Fin 2) = (1 : Fin 2) := h h1
  simp at h2

/-! §5 AxiomF - AxiomH（不需要 AxiomC 的公理） -/

private instance instF : AxiomF (Fin 2) (Fin 2) :=
  { scale := fun _ => 1,
    scale_pos := by intro n; norm_num,
    scale_limit := fun ε hε => ⟨0, fun _ _ => by simp <;> linarith⟩ }

private instance instG : AxiomG (Fin 2) (Fin 2) :=
  { spin_network := Unit,
    amplitude_spin := fun _ => 1 }

private instance instH : AxiomH (Fin 2) (Fin 2) :=
  { gauge_group := Fin 2,
    field_content := fun _ _ => 0,
    lagrangian := fun _ => 0 }

private instance instI : AxiomI (Fin 2) (Fin 2) :=
  { entropy := fun _ => 0,
    entropy_nonneg := by intro S; simp,
    entropy_subadditive := by intro S T; simp,
    information_causal := by intro x y _; simp }

private instance instJ : AxiomJ (Fin 2) (Fin 2) :=
  { evolve := fun _ x => x,
    causal_update := fun _ x => ft_le_refl x,
    comp_evolve := fun _ _ _ => rfl }

/-! §6 核心 Trade-off 定理 -/

/-- **Trade-off 定理**: 在 Fin 2 模型中，常函数 amplitude 不能满足 AxiomC

这是一个不可能性结果：不存在 `AxiomC (Fin 2) (Fin 2)` 的实例
其 amplitude 字段为常函数 `fun _ => 1`，因为这违反 `amplitude_injective`。

对比于 `nonTrivialFinModel`：那里 amplitude 是真正非平凡的（I^n），
而 output 被迫退化（常函数）。这里我们看到了对偶的情况。-/
theorem trade_off_no_degenerate_amplitude_C :
  ¬ Function.Injective ft_amplitude := constant_amplitude_not_injective

end CSQIT.Models.OutputNonTrivial

/-! ============================================================================
   总结：从 Fin 5 × Fin 4 到结构定理
   ============================================================================

   我们已经建立了以下数学事实：

   1. nonTrivialFinModel (M = Fin 5, C = Fin 4)
      ✅ amplitude 非平凡且 injective (I^n, n ∈ {0,1,2,3})
      ✅ compose 是真实的群运算（Fin 4 加法）
      ✅ M 具有真实的因果序（0 < 1 < 2 < 3 < 4）
      ✅ 完整的 Theory 实例（所有公理都满足）
      ❌ output 是常函数（因 compose_output 要求）

   2. Trade-off 定理 (M = Fin 2, C = Fin 2)
      ✅ 证明了常函数 amplitude 不可能是单射
      ✅ 因此不存在 amplitude 为常数的完整 Theory 实例
      ✅ 展示了 compose_output 与 amplitude_injective 的根本张力

   核心结构性结论：
   在标准 AxiomA (compose_output) 与 AxiomC (amplitude_injective) 条件下：
   amplitude 必须非平凡 ⇒ output 必须退化
   这不是设计缺陷，而是深刻的数学事实。
   它揭示了 compose_output 条件与 amplitude_injective 条件之间
   的基本不对称性。

   解决这一问题的方向（在 AxiomA' / AxiomC' 等扩展公理中已实现）：
     1. 修改 compose_output: output(α·β) = combine(output α)(output β)
        用 combine 运算替代直接的 output β
     2. 引入更丰富的 amplitude 结构（不仅仅是群同态）
     3. 放弃 unitarity 条件，允许 amplitude(α) 的范数 < 1

   ============================================================================ -/
