/-
================================================================================
CSQIT — 因果格与 AxiomA' 的兼容性桥梁
文件: Core/W1/CausalLatticeToAxiomA.lean
版本: v11.6.0
日期: 2026-07-15

================================================================================
理论层级说明
================================================================================

本文件属于 **W1.5 层**——介于形式化数学(W1)与概念框架(W2)之间。

- 所有定义均为精确的 Lean 4 形式化（W1 标准）
- 定理分为两部分：
  · 纯格论部分：使用标准库 Lattice，有严格证明
  · 物理诠释部分：为 W2/W3 层的概念框架
- 核心贡献：建立因果格理论与 CSQIT 公理体系的数学对应

================================================================================
v11.6.3 更新说明
================================================================================

为确保证明可编译，本版本采用以下策略：

1. **使用标准库类型类**：仅使用 `Preorder`、`PartialOrder`、`Lattice`，
   避免使用继承自 AxiomB 的 `CausalLattice` 类型类，以规避类型类冲突。

2. **路径组合用 Prop 描述**：由于 `CausalSite` 缺少 `DecidableEq` 实例，
   将 `compPath` 从可执行函数改为关系/性质描述，避免 `if h : ...` 失败。

3. **格引理显式标注类型**：所有标准库引理（sup_assoc 等）显式标注类型参数，
   避免 universe/类型参数未统一导致的类型不匹配。

4. **概念性构造使用 Prop**：完整 AxiomA' 实例构造等长期目标以 Prop 形式保留，
   确保文件可编译且不牺牲理论方向。

================================================================================
-/

import Mathlib.Order.Lattice
import Mathlib.Tactic

universe u v

namespace CSQIT.CausalLatticeToAxiomA

/-! ============================================================================
   §1. 因果路径结构（严格定义）
   ============================================================================ -/

/--
**定义 1.1: 因果路径**

给定一个带偏序的类型 M，因果路径是一个有序对 (source, target)，
满足 source ≤ target。
-/
structure CausalPath (M : Type*) [Preorder M] where
  source : M
  target : M
  causal_valid : source ≤ target

namespace CausalPath

variable {M : Type*} [Preorder M]

/-- 平凡路径（起点 = 终点），对应恒等规则 -/
def refl (x : M) : CausalPath M :=
  ⟨x, x, le_refl x⟩

/-- 路径的起点投影（对应 AxiomA' 的 output） -/
def src (p : CausalPath M) : M := p.source

/-- 路径的终点投影 -/
def tgt (p : CausalPath M) : M := p.target

end CausalPath

/-! ============================================================================
   §2. 路径组合（关系描述，避免 DecidableEq 要求）
   ============================================================================ -/

/--
**定义 2.1: 因果路径的顺序复合关系**

两条路径 p : a→b 和 q : b→c 可以复合为 r : a→c，
当且仅当 p.target = q.source 且 r.source = p.source、r.target = q.target。

这里用关系（Prop）而非函数（Option）来定义，
以避免 `CausalSite` 上 `DecidableEq` 实例缺失导致的编译问题。
-/
def CompPathRel {M : Type*} [Preorder M]
    (p q r : CausalPath M) : Prop :=
  p.target = q.source ∧ r.source = p.source ∧ r.target = q.target

/--
**定理 2.1: 路径复合保持因果有效性**

如果 p : a→b 和 q : b→c 可复合为 r，则 r : a→c 也是有效因果路径。
-/
theorem compPath_valid {M : Type*} [Preorder M]
    {p q r : CausalPath M} (h : CompPathRel p q r) :
    r.source ≤ r.target := by
  rcases h with ⟨h_mid, h_source, h_target⟩
  rw [h_source, h_target]
  exact le_trans p.causal_valid (h_mid ▸ q.causal_valid)

/-! ============================================================================
   §3. 格运算的基本性质（严格证明，显式类型标注）
   ============================================================================ -/

section LatticeProperties

variable {M : Type*} [Lattice M]

/-- 格并运算的结合律 -/
theorem sup_assoc' (a b c : M) : (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c) :=
  @sup_assoc M _ a b c

/-- 格并运算的交换律 -/
theorem sup_comm' (a b : M) : a ⊔ b = b ⊔ a :=
  @sup_comm M _ a b

/-- 格并运算的幂等律 -/
theorem sup_idem' (a : M) : a ⊔ a = a :=
  @sup_idem M _ a

/-- 格交运算的结合律 -/
theorem inf_assoc' (a b c : M) : (a ⊓ b) ⊓ c = a ⊓ (b ⊓ c) :=
  @inf_assoc M _ a b c

/-- 吸收律 -/
theorem absorb_sup_inf (a b : M) : a ⊔ (a ⊓ b) = a :=
  @sup_inf_self M _ a b

theorem absorb_inf_sup (a b : M) : a ⊓ (a ⊔ b) = a :=
  @inf_sup_self M _ a b

end LatticeProperties

/-! ============================================================================
   §4. 因果格 → AxiomA' 的兼容性（严格定理）
   ============================================================================ -/

section Compatibility

variable {M C : Type*} [Lattice M]
variable (output : C → M) (compose : C → C → C)

/-- output 是格同态的条件 -/
def OutputSupHomomorphism : Prop :=
  ∀ (α β : C), output (compose α β) = output α ⊔ output β

/--
**定理 4.1: 如果 output 是格同态且 compose 满足结合律，
   则 output 的像上的 combine (= ⊔) 也满足结合律**
-/
theorem combine_assoc_from_lattice
    (h_compose_assoc : ∀ (α β γ : C), compose (compose α β) γ = compose α (compose β γ))
    (h_hom : OutputSupHomomorphism output compose) :
    ∀ (α β γ : C),
      (output α ⊔ output β) ⊔ output γ = output α ⊔ (output β ⊔ output γ) := by
  intro α β γ
  have h1 : (output α ⊔ output β) ⊔ output γ = output (compose (compose α β) γ) := by
    rw [h_hom (compose α β) γ, h_hom α β]
  have h2 : output α ⊔ (output β ⊔ output γ) = output (compose α (compose β γ)) := by
    rw [h_hom α (compose β γ), h_hom β γ]
  rw [h1, h2, h_compose_assoc α β γ]

/--
**定理 4.2: output 格同态 → output 非退化的充分条件**
-/
theorem output_nondeg_from_hom
    (h_hom : OutputSupHomomorphism output compose)
    (h_exists : ∃ (α β : C), output α ≠ output β) :
    ¬ ∃ (x : M), ∀ (α : C), output α = x := by
  intro h
  rcases h with ⟨x, hx⟩
  rcases h_exists with ⟨α, β, hne⟩
  have h1 : output α = x := hx α
  have h2 : output β = x := hx β
  rw [h1, h2] at hne
  exact ne_of_apply_ne (fun y => y) hne (rfl)

end Compatibility

/-! ============================================================================
   §5. 格序与因果序的对应（严格定理）
   ============================================================================ -/

/--
**定理 5.1: 格序可以从并运算恢复**

x ≤ y ↔ x ⊔ y = y
-/
theorem sup_determines_order {M : Type*} [Lattice M] (x y : M) :
    x ≤ y ↔ x ⊔ y = y := by
  constructor
  · -- →
    intro h
    have h1 : x ⊔ y ≤ y := by
      apply sup_le
      · exact h
      · exact le_refl y
    have h2 : y ≤ x ⊔ y := le_sup_right
    exact le_antisymm h1 h2
  · -- ←
    intro h
    have h' : x ≤ x ⊔ y := le_sup_left
    rw [h] at h'
    exact h'

/--
**定理 5.2: 并运算的单调性**
-/
theorem sup_monotone {M : Type*} [Lattice M] {x₁ x₂ y₁ y₂ : M}
    (h₁ : x₁ ≤ y₁) (h₂ : x₂ ≤ y₂) :
    x₁ ⊔ x₂ ≤ y₁ ⊔ y₂ :=
  sup_le_sup h₁ h₂

/-! ============================================================================
   §6. 概念性陈述（待严格化，以 Prop 形式保留）
   ============================================================================ -/

/--
**输入规则空间**：由格元素生成的有限多重集

    每个规则 α 由其输入列表 [a₁, a₂, ..., aₙ] 和输出 b 组成，
    满足 ⨆{a₁, ..., aₙ} = b。
-/
def listSup {M : Type*} [Lattice M] [OrderBot M] (xs : List M) : M :=
  xs.foldr (· ⊔ ·) ⊥

structure InputRule (M : Type*) [Lattice M] [OrderBot M] where
  inputs : List M
  output : M
  closure_prop : listSup inputs = output

/-- **单位规则**：空输入，输出为格的最小元 -/
def inputRuleUnit {M : Type*} [Lattice M] [OrderBot M] : InputRule M :=
  ⟨[], ⊥, rfl⟩

/-- **单点规则**：输入为单个元素，输出为同一元素 -/
def inputRuleSingl {M : Type*} [Lattice M] [OrderBot M] (a : M) : InputRule M :=
  ⟨[a], a, by
    unfold listSup
    rw [List.foldr_cons]
    apply sup_bot_eq⟩

/-- **规则复合**：输入合并，输出取并 -/
def inputRuleComp {M : Type*} [Lattice M] [OrderBot M] (r₁ r₂ : InputRule M) : InputRule M :=
  ⟨r₁.inputs ++ r₂.inputs, r₁.output ⊔ r₂.output, by
    -- 辅助引理: listSup (xs ++ ys) = listSup xs ⊔ listSup ys
    have h_split : ∀ (xs ys : List M), listSup (xs ++ ys) = listSup xs ⊔ listSup ys := by
      intro xs ys
      induction xs with
      | nil =>
        simp [listSup]
      | cons x xs ih =>
        rw [List.cons_append]
        have h_def1 : listSup (x :: (xs ++ ys)) = x ⊔ listSup (xs ++ ys) :=
          List.foldr_cons
        have h_def2 : listSup (x :: xs) = x ⊔ listSup xs :=
          List.foldr_cons
        rw [h_def1, h_def2, ih]
        exact (sup_assoc x (listSup xs) (listSup ys)).symm
    rw [h_split, r₁.closure_prop, r₂.closure_prop]⟩

/--
**猜想 6.1: 因果格诱导完整 AxiomA' 实例**

存在一个从格 M 构造的规则空间 C，
使得 AxiomA' M C 成立，且 output 是格同态。

注意：完整构造需要处理 input 字段问题，此处作为研究方向保留。
-/
def CausalLatticeInducesAxiomA' (M : Type u) [Lattice M] : Prop :=
  ∃ (C : Type u)
    (input : C → List M)
    (output : C → M)
    (compose : C → C → C)
    (_input_nodup : ∀ α, (input α).Nodup)
    (_compose_input : ∀ α β, input (compose α β) = input α ++ input β)
    (_compose_output' : ∀ α β, output (compose α β) = output α ⊔ output β)
    (_compose_assoc : ∀ α β γ, compose (compose α β) γ = compose α (compose β γ)),
    True

/--
**猜想 6.2: 因果格解决三大结构性解耦**
-/
def CausalLatticeSolvesThreeDecouplings (M : Type u) [Lattice M] : Prop :=
  CausalLatticeInducesAxiomA' M → True

/--
**猜想 6.3: 输入规则空间构成幺半群**

在有限格上，输入规则的复合运算构成幺半群。
-/
def InputRuleMonoid (M : Type*) [Lattice M] [OrderBot M] : Prop :=
  ∀ (r₁ r₂ r₃ : InputRule M),
    (inputRuleComp (inputRuleComp r₁ r₂) r₃) = inputRuleComp r₁ (inputRuleComp r₂ r₃) ∧
    inputRuleComp r₁ inputRuleUnit = r₁ ∧
    inputRuleComp inputRuleUnit r₁ = r₁

/-! ============================================================================
   总结
   ============================================================================

本文件已完成的严格证明（W1 标准）：

✅ **因果路径结构**
   - CausalPath M：带 source ≤ target 条件的有序对
   - refl：平凡路径
   - CompPathRel：路径复合关系

✅ **格运算基本性质**
   - sup_assoc, sup_comm, sup_idem
   - inf_assoc
   - 吸收律

✅ **因果格 → AxiomA' 兼容性**
   - OutputSupHomomorphism
   - combine_assoc_from_lattice
   - output_nondeg_from_hom

✅ **格序与因果序的对应**
   - sup_determines_order
   - sup_monotone

🔶 **概念性陈述（待严格化）**
   - 完整 AxiomA' 实例的构造
   - 三大结构性解耦的解决方案
================================================================================ -/

end CSQIT.CausalLatticeToAxiomA
