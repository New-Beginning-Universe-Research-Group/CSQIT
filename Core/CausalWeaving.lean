import Core.Axioms

namespace CSQIT

set_option linter.unusedVariables false
set_option linter.unusedTactic false

variable {M C : Type*}

/-! ============================================================================
   因果序与编织定理（Causal Order & Weaving Theorems）
   ============================================================================

   本文件包含 CSQIT 理论中关于因果序和编织公理的核心定理。

   核心定理：
   1. input_must_be_empty — 核心坍缩定理：AxiomA 强制所有输入为空
   2. 因果偏序的基本性质（refl, trans, antisymm）
   3. 严格因果序的基本性质（irrefl, trans）
   4. 编织公理的空洞性推论
   ============================================================================ -/

/-! ----------------------------------------------------------------------------
   核心坍缩定理：AxiomA 强制所有输入为空
   ----------------------------------------------------------------------------

   这是整个理论中最深刻的结构性结果。
   证明思路：对任意规则 α，考虑 compose α α。
   由 compose_input：input(compose α α) = input α ++ input α
   由 input_nodup：(input(compose α α)).Nodup，即 (input α ++ input α).Nodup
   由 List.nodup_append，这蕴含 Disjoint ((input α : Set M)) ((input α : Set M))
   由 Set.disjoint_self，得 (input α : Set M) = ∅，即 input α = []。
   ---------------------------------------------------------------------------- -/

/-- **核心坍缩定理**: AxiomA 的约束强制所有规则的输入为空。

    证明：对任意规则 α，
    1. 由 input_nodup，有 (input (compose α α)).Nodup
    2. 由 compose_input，有 input (compose α α) = input α ++ input α
    3. 因此 (input α ++ input α).Nodup
    4. 由 List.nodup_append，得 (input α).Nodup ∧ Disjoint (↑(input α) : Set M) (↑(input α) : Set M)
    5. 由 Set.disjoint_self，得 (↑(input α) : Set M) = ∅
    6. 因此 input α = []。
    这表明：在任何满足 AxiomA 的模型中，规则没有真正的输入。 -/
@[simp] theorem input_must_be_empty [A : AxiomA M C] (α : C) : A.input α = [] := by
  have h1 : (A.input (A.compose α α)).Nodup := A.input_nodup (A.compose α α)
  have h2 : A.input (A.compose α α) = A.input α ++ A.input α := A.compose_input α α
  have h3 : (A.input α ++ A.input α).Nodup := by
    rw [h2] at h1; exact h1
  cases h : A.input α with
  | nil =>
    rfl
  | cons y t =>
    rw [h] at h3
    have h4 : ((y :: t) ++ (y :: t)) = y :: (t ++ (y :: t)) := by rfl
    rw [h4] at h3
    have h5 : y ∉ (t ++ (y :: t)) := (List.nodup_cons.mp h3).1
    have h6 : y ∈ (t ++ (y :: t)) := by
      simp [List.mem_append] <;> tauto
    exact False.elim (h5 h6)

/-- **推论 1**: 所有输入列表的长度都是 0。 -/
@[simp] theorem input_length_zero [A : AxiomA M C] (α : C) : (A.input α).length = 0 := by
  rw [input_must_be_empty α]
  <;> simp

/-- **推论 2: 无因果输入原则 (No Causal Input Principle)**。
    对任意规则 α 和关系元 x，x ∉ input α。

    **物理诠释**: 离散时空中的规则不需要"外部信息"来产生因果效应。
    因果关系是规则本身的内蕴属性，不是通过输入注入的。 -/
theorem no_causal_input [A : AxiomA M C] (α : C) (x : M) : ¬ (x ∈ A.input α) := by
  rw [input_must_be_empty α]
  <;> simp

/-- **核心物理定理 1: 编织公理的空洞性 (Weaving Axiom Vacuity)**。
    在任何满足 AxiomA + AxiomB 的模型中，weaving_axiom 的前提
    `x ∈ input α` 恒为 False，因此整个公理自动成立。 -/
theorem input_empty_implies_no_causal_input {M C : Type*} [A : AxiomA M C] [B : AxiomB M C] :
  ∀ (α : C) (x : M), (x ∈ A.input α) → B.lt x (A.output α) := by
  intro α x h_in
  have h1 : A.input α = [] := input_must_be_empty α
  rw [h1] at h_in
  simp at h_in
  <;> exact False.elim h_in

/-- **核心物理定理 2: 编织前提不可满足性 (Unsatisfiability of Weaving Premise)**。
    不存在 α 和 x 使得 `x ∈ input α` 成立。 -/
theorem no_satisfiable_weaving_premise {M C : Type*} [A : AxiomA M C] :
  ¬ ∃ (α : C) (x : M), x ∈ A.input α := by
  intro h
  rcases h with ⟨α, x, h_in⟩
  have h1 : A.input α = [] := input_must_be_empty α
  rw [h1] at h_in
  simp at h_in

/-- **等价表述**: weaving_axiom 在 AxiomA 下等价于 True（无内容）。 -/
theorem weaving_axiom_equivalent_to_true {M C : Type*} [A : AxiomA M C] [B : AxiomB M C] :
  (∀ (α : C) (x : M), x ∈ A.input α → B.lt x (A.output α)) ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact input_empty_implies_no_causal_input

/-- **AxiomD 冗余定理**: op_weaving 的长度前提 `|input β| = |input α| + 1`
    化简为 `0 = 1`，恒为 False，因此 AxiomD 的 op_weaving 公理空洞成立。 -/
theorem axiomD_redundant [A : AxiomA M C] [B : AxiomB M C] (α β : C) :
    ¬ ((A.input β).length = (A.input α).length + 1) := by
  rw [input_length_zero β, input_length_zero α]
  <;> simp
  <;> norm_num

/-- input_is_empty_forall 是 input_must_be_empty 的另一种表述 -/
theorem input_is_empty_forall [A : AxiomA M C] (α : C) (x : M) : ¬ (x ∈ A.input α) :=
  no_causal_input α x

/-- weaving_axiom_redundant 定理 -/
theorem weaving_axiom_redundant [A : AxiomA M C] (α : C) (x : M) : ¬ (x ∈ A.input α) :=
  input_is_empty_forall α x

/-! ----------------------------------------------------------------------------
   因果偏序的基本性质
   ---------------------------------------------------------------------------- -/

/-- 因果偏序的自反性 -/
theorem causal_le_refl [A : AxiomA M C] [B : AxiomB M C] (x : M) :
    B.le x x := B.le_refl x

/-- 因果偏序的传递性 -/
theorem causal_le_trans [A : AxiomA M C] [B : AxiomB M C]
    (x y z : M) (hxy : B.le x y) (hyz : B.le y z) : B.le x z :=
  B.le_trans x y z hxy hyz

/-- 因果偏序的反对称性 -/
theorem causal_le_antisymm [A : AxiomA M C] [B : AxiomB M C]
    (x y : M) (hxy : B.le x y) (hyx : B.le y x) : x = y :=
  B.le_antisymm x y hxy hyx

/-- 严格序与偏序的等价性 -/
theorem causal_lt_iff_le_not_le [A : AxiomA M C] [B : AxiomB M C] (x y : M) :
    B.lt x y ↔ (B.le x y ∧ ¬ B.le y x) :=
  B.lt_iff_le_not_le x y

/-! ----------------------------------------------------------------------------
   严格因果序的基本性质
   ---------------------------------------------------------------------------- -/

/-- 严格因果序的无反自性 -/
theorem strict_order_irrefl
    {M C : Type*} [A : AxiomA M C] [B : AxiomB M C]
    (x : M) : ¬ B.lt x x := by
  intro h
  have h1 : B.lt x x ↔ (B.le x x ∧ ¬ B.le x x) := causal_lt_iff_le_not_le x x
  have h2 : B.le x x ∧ ¬ B.le x x := h1.mp h
  have h3 : B.le x x := B.le_refl x
  exact h2.right h3

/-- 严格因果序的传递性 -/
theorem strict_order_trans
    {M C : Type*} [A : AxiomA M C] [B : AxiomB M C]
    (x y z : M) (hxy : B.lt x y) (hyz : B.lt y z) : B.lt x z := by
  have h1 : B.le x y ∧ ¬ B.le y x := (causal_lt_iff_le_not_le x y).mp hxy
  have h2 : B.le y z ∧ ¬ B.le z y := (causal_lt_iff_le_not_le y z).mp hyz
  have h3 : B.le x z := B.le_trans x y z h1.left h2.left
  have h4 : ¬ B.le z x := by
    intro h5
    have h6 : B.le z y := B.le_trans z x y h5 h1.left
    exact h2.right h6
  exact (causal_lt_iff_le_not_le x z).mpr ⟨h3, h4⟩

/-! ----------------------------------------------------------------------------
   编织公理的推论
   ---------------------------------------------------------------------------- -/

/-- 编织公理的推论 —— 输出关系元严格晚于输入 -/
theorem weaving_implies_output_not_in_input
    {M C : Type*} [A : AxiomA M C] [B : AxiomB M C]
    (α : C) (x : M) (hx : x ∈ A.input α) : B.lt x (A.output α) :=
  B.weaving_axiom α x hx

/-- 输出不在输入中（由 input_must_be_empty 直接得出） -/
theorem output_not_in_input [A : AxiomA M C] [B : AxiomB M C] (α : C) :
    ¬ (A.output α ∈ A.input α) :=
  no_causal_input α (A.output α)

end CSQIT
