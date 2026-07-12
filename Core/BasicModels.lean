import Core.Axioms
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Finite.Basic

namespace CSQIT

set_option linter.unusedVariables false
set_option linter.unusedTactic false

/-! ============================================================================
   基础模型构造（Basic Models）
   ============================================================================

   本文件包含 CSQIT 理论的基础具体模型构造，用于：
   1. 证明理论的一致性（存在非空模型）
   2. 提供具体的数学实例，帮助理解抽象公理
   3. 作为检验新定理的试验场

   模型列表：
   - trivialModel : Theory Unit Unit     （平凡模型，一切退化）
   - boolModel    : Theory Bool Unit     （Bool 模型，两个关系元态）
   ============================================================================ -/

/-! ----------------------------------------------------------------------------
   模型 1: 平凡模型 (trivialModel)
   最简单的模型：所有关系元和规则都是 Unit 类型
   ---------------------------------------------------------------------------- -/

namespace trivialModel

private def trivial_input : Unit → List Unit := fun (_ : Unit) => []
private def trivial_output : Unit → Unit := fun (_ : Unit) => ()
private def trivial_compose : Unit → Unit → Unit := fun (_ : Unit) (_ : Unit) => ()
private def trivial_le (_ _ : Unit) : Prop := True
private def trivial_lt (_ _ : Unit) : Prop := False
private def trivial_amplitude (_ : Unit) : ℂ := (1 : ℂ)
private def trivial_scale (n : ℕ) : ℝ := (1 : ℝ)
private def trivial_entropy (_ : Set Unit) : ℝ := (0 : ℝ)
private def trivial_field_content (_ : Unit) (_ : Unit) : ℂ := (0 : ℂ)
private def trivial_lagrangian (_ : Unit → ℂ) : ℝ := (0 : ℝ)

private lemma trivial_input_nodup (α : Unit) : (trivial_input α).Nodup := by
  cases α <;> simp [trivial_input, List.Nodup]

private lemma trivial_compose_input (α β : Unit) :
    trivial_input (trivial_compose α β) = trivial_input α ++ trivial_input β := by
  cases α <;> cases β <;> simp [trivial_input, trivial_compose]

private lemma trivial_compose_output (α β : Unit) :
    trivial_output (trivial_compose α β) = trivial_output β := by
  cases α <;> cases β <;> simp [trivial_output, trivial_compose]

private lemma trivial_compose_assoc (α β γ : Unit) :
    trivial_compose (trivial_compose α β) γ = trivial_compose α (trivial_compose β γ) := by
  cases α <;> cases β <;> cases γ <;> simp [trivial_compose]

private lemma trivial_le_refl (x : Unit) : trivial_le x x := by
  cases x <;> simp [trivial_le]

private lemma trivial_le_trans (x y z : Unit) (hxy : trivial_le x y) (hyz : trivial_le y z) :
    trivial_le x z := by
  cases x <;> cases y <;> cases z <;> simp [trivial_le]

private lemma trivial_le_antisymm (x y : Unit) (hxy : trivial_le x y) (hyx : trivial_le y x) :
    x = y := by
  cases x <;> cases y <;> rfl

private lemma trivial_lt_iff (x y : Unit) :
    trivial_lt x y ↔ (trivial_le x y ∧ ¬ trivial_le y x) := by
  cases x <;> cases y <;> simp [trivial_le, trivial_lt]

private lemma trivial_localFinite_past (x : Unit) : Set.Finite { y : Unit | trivial_lt y x } := by
  haveI : Fintype Unit := inferInstance
  exact Set.toFinite _

private lemma trivial_localFinite_future (x : Unit) : Set.Finite { y : Unit | trivial_lt x y } := by
  haveI : Fintype Unit := inferInstance
  exact Set.toFinite _

private lemma trivial_weaving_axiom (α : Unit) (x : Unit) (hx : x ∈ trivial_input α) :
    trivial_lt x (trivial_output α) := by
  cases α
  have hdef : (trivial_input () : List Unit) = [] := by rfl
  rw [hdef] at hx
  simp at hx

private lemma trivial_amplitude_norm_one (α : Unit) :
    Complex.normSq (trivial_amplitude α) = 1 := by
  cases α <;> simp [trivial_amplitude, Complex.normSq] <;> norm_num

private lemma trivial_amplitude_comp (α β : Unit) :
    trivial_amplitude (trivial_compose α β) = trivial_amplitude α * trivial_amplitude β := by
  cases α <;> cases β <;> simp [trivial_amplitude, trivial_compose] <;> ring

private lemma trivial_amplitude_injective :
    Function.Injective trivial_amplitude := by
  intro x y _
  cases x <;> cases y <;> rfl

private lemma trivial_scale_pos (n : ℕ) : 0 < trivial_scale n := by
  simp [trivial_scale] <;> norm_num

private lemma trivial_scale_limit :
    ∀ ε > 0, ∃ N, ∀ n > N, |trivial_scale n - trivial_scale (n + 1)| < ε := by
  intro ε hε
  refine ⟨0, fun _ _ => by simp [trivial_scale] <;> norm_num <;> exact hε⟩

private lemma trivial_entropy_nonneg (S : Set Unit) : 0 ≤ trivial_entropy S := by
  exact show (0 : ℝ) ≤ (0 : ℝ) from by norm_num

private lemma trivial_entropy_subadditive (S T : Set Unit) :
    trivial_entropy (S ∪ T) ≤ trivial_entropy S + trivial_entropy T := by
  exact show (0 : ℝ) ≤ (0 : ℝ) + (0 : ℝ) from by norm_num

private lemma trivial_information_causal (x y : Unit) (h : trivial_le x y) :
    trivial_entropy {z | trivial_le z x} ≤ trivial_entropy {z | trivial_le z y} := by
  exact show (0 : ℝ) ≤ (0 : ℝ) from by norm_num

private def trivial_evolve (_ : Unit) (_ : Unit) : Unit := ()

private lemma trivial_causal_update (α : Unit) (x : Unit) :
    trivial_le x (trivial_evolve α x) := by
  trivial

private lemma trivial_comp_evolve (α β : Unit) (x : Unit) :
    trivial_evolve (trivial_compose α β) x = trivial_evolve β (trivial_evolve α x) := by
  rfl

private instance instA : AxiomA Unit Unit :=
  { input := trivial_input,
    output := trivial_output,
    input_nodup := trivial_input_nodup,
    compose := trivial_compose,
    compose_input := trivial_compose_input,
    compose_output := trivial_compose_output,
    compose_assoc := trivial_compose_assoc }

private instance instB : AxiomB Unit Unit :=
  { le := trivial_le,
    lt := trivial_lt,
    le_refl := trivial_le_refl,
    le_trans := trivial_le_trans,
    le_antisymm := trivial_le_antisymm,
    lt_iff_le_not_le := trivial_lt_iff,
    localFinite_past := trivial_localFinite_past,
    localFinite_future := trivial_localFinite_future,
    weaving_axiom := trivial_weaving_axiom }

private instance instD : AxiomD Unit Unit :=
  { op_weaving := by
      intro α β hlt
      cases hlt }

private instance instC : AxiomC Unit Unit :=
  { amplitude := trivial_amplitude,
    norm_one := trivial_amplitude_norm_one,
    comp_rule := trivial_amplitude_comp,
    amplitude_injective := trivial_amplitude_injective }

private instance instF : AxiomF Unit Unit :=
  { scale := trivial_scale,
    scale_pos := trivial_scale_pos,
    scale_limit := trivial_scale_limit }

private instance instG : AxiomG Unit Unit :=
  { spin_network := Unit,
    amplitude_spin := fun (_ : Unit) => (1 : ℂ) }

private instance instH : AxiomH Unit Unit :=
  { gauge_group := Unit,
    field_content := trivial_field_content,
    lagrangian := trivial_lagrangian }

private instance instI : @AxiomI Unit Unit instA instB :=
  { entropy := trivial_entropy,
    entropy_nonneg := trivial_entropy_nonneg,
    entropy_subadditive := trivial_entropy_subadditive,
    information_causal := trivial_information_causal }

private instance instJ : AxiomJ Unit Unit :=
  { evolve := fun (_ : Unit) (_ : Unit) => (),
    causal_update := by
      intro α x
      trivial,
    comp_evolve := by
      intro α β x
      rfl }

end trivialModel

/-- 平凡模型 (trivialModel) -/
def trivialModel : Theory Unit Unit :=
  { toAxiomA := trivialModel.instA,
    toAxiomB := trivialModel.instB,
    toAxiomD := trivialModel.instD,
    toAxiomC := trivialModel.instC,
    toAxiomF := trivialModel.instF,
    toAxiomG := trivialModel.instG,
    toAxiomH := trivialModel.instH,
    toAxiomI := trivialModel.instI,
    toAxiomJ := trivialModel.instJ }

/-! ----------------------------------------------------------------------------
   模型 2: Bool 模型 (boolModel)
   非平凡模型：M = Bool（两个关系元态），C = Unit（一个规则）
   ---------------------------------------------------------------------------- -/

namespace boolModel

private def bool_input : Unit → List Bool := fun (_ : Unit) => []
private def bool_output : Unit → Bool := fun (_ : Unit) => false
private def bool_compose : Unit → Unit → Unit := fun (_ : Unit) (_ : Unit) => ()
private def bool_le : Bool → Bool → Prop := fun (x : Bool) (y : Bool) => x = false ∨ y = true
private def bool_lt : Bool → Bool → Prop := fun (x : Bool) (y : Bool) => x = false ∧ y = true
private def bool_amplitude : Unit → ℂ := fun (_ : Unit) => (1 : ℂ)
private def bool_scale : ℕ → ℝ := fun (_ : ℕ) => (1 : ℝ)
private def bool_entropy : Set Bool → ℝ := fun (_ : Set Bool) => (0 : ℝ)
private def bool_field_content : Unit → Bool → ℂ := fun (_ : Unit) (_ : Bool) => (0 : ℂ)
private def bool_lagrangian : (Bool → ℂ) → ℝ := fun (_ : Bool → ℂ) => (0 : ℝ)

private lemma bool_input_nodup (c : Unit) : (bool_input c).Nodup := by
  cases c <;> simp [bool_input, List.Nodup]

private lemma bool_compose_input (α β : Unit) :
    bool_input (bool_compose α β) = bool_input α ++ bool_input β := by
  cases α <;> cases β <;> simp [bool_input, bool_compose]

private lemma bool_compose_output (α β : Unit) :
    bool_output (bool_compose α β) = bool_output β := by
  cases α <;> cases β <;> simp [bool_output, bool_compose]

private lemma bool_compose_assoc (α β γ : Unit) :
    bool_compose (bool_compose α β) γ = bool_compose α (bool_compose β γ) := by
  cases α <;> cases β <;> cases γ <;> simp [bool_compose]

private lemma bool_le_refl (x : Bool) : bool_le x x := by
  cases x <;> simp [bool_le]

private lemma bool_le_trans (x y z : Bool) (hxy : bool_le x y) (hyz : bool_le y z) :
    bool_le x z := by
  cases x <;> cases y <;> cases z <;> simp [bool_le] at hxy hyz ⊢ <;> tauto

private lemma bool_le_antisymm (x y : Bool) (hxy : bool_le x y) (hyx : bool_le y x) : x = y := by
  cases x <;> cases y <;> simp [bool_le] at hxy hyx ⊢ <;> tauto

private lemma bool_lt_iff (x y : Bool) :
    bool_lt x y ↔ (bool_le x y ∧ ¬ bool_le y x) := by
  cases x <;> cases y <;> simp [bool_le, bool_lt] <;> tauto

private lemma bool_localFinite_past (x : Bool) : Set.Finite { y : Bool | bool_lt y x } := by
  haveI : Fintype Bool := inferInstance
  exact Set.toFinite _

private lemma bool_localFinite_future (x : Bool) : Set.Finite { y : Bool | bool_lt x y } := by
  haveI : Fintype Bool := inferInstance
  exact Set.toFinite _

private lemma bool_weaving_axiom (α : Unit) (x : Bool) (hx : x ∈ bool_input α) :
    bool_lt x (bool_output α) := by
  cases α
  have hdef : (bool_input () : List Bool) = [] := by rfl
  rw [hdef] at hx
  simp at hx

private lemma bool_op_weaving (α β : Unit) (hlt : bool_lt (bool_output α) (bool_output β)) :
    ∃ (γ : Unit), bool_compose α γ = β := by
  rcases hlt with ⟨h1, h2⟩
  exact ⟨(), rfl⟩

private lemma bool_amplitude_norm_one (α : Unit) :
    Complex.normSq (bool_amplitude α) = 1 := by
  cases α <;> simp [bool_amplitude, Complex.normSq]

private lemma bool_amplitude_comp (α β : Unit) :
    bool_amplitude (bool_compose α β) = bool_amplitude α * bool_amplitude β := by
  cases α <;> cases β <;> simp [bool_amplitude, bool_compose]

private lemma bool_amplitude_injective :
    Function.Injective bool_amplitude := by
  intro x y _
  cases x <;> cases y <;> rfl

private lemma bool_scale_pos (n : ℕ) : 0 < bool_scale n := by
  simp [bool_scale] <;> norm_num

private lemma bool_scale_limit :
    ∀ ε > 0, ∃ N, ∀ n > N, |bool_scale n - bool_scale (n + 1)| < ε := by
  intro ε hε
  refine ⟨0, fun _ _ => by simp [bool_scale] <;> norm_num <;> exact hε⟩

private lemma bool_entropy_nonneg (S : Set Bool) : 0 ≤ bool_entropy S := by
  exact show (0 : ℝ) ≤ (0 : ℝ) from by norm_num

private lemma bool_entropy_subadditive (S T : Set Bool) :
    bool_entropy (S ∪ T) ≤ bool_entropy S + bool_entropy T := by
  exact show (0 : ℝ) ≤ (0 : ℝ) + (0 : ℝ) from by norm_num

private lemma bool_information_causal (x y : Bool) (h : bool_le x y) :
    bool_entropy {z | bool_le z x} ≤ bool_entropy {z | bool_le z y} := by
  exact show (0 : ℝ) ≤ (0 : ℝ) from by norm_num

private def bool_evolve (_ : Unit) (x : Bool) : Bool := x

private lemma bool_causal_update (α : Unit) (x : Bool) :
    bool_le x (bool_evolve α x) := by
  cases x
  · left; rfl
  · right; rfl

private lemma bool_comp_evolve (α β : Unit) (x : Bool) :
    bool_evolve (bool_compose α β) x = bool_evolve β (bool_evolve α x) := by
  rfl

private instance instA : AxiomA Bool Unit :=
  { input := bool_input,
    output := bool_output,
    input_nodup := bool_input_nodup,
    compose := bool_compose,
    compose_input := bool_compose_input,
    compose_output := bool_compose_output,
    compose_assoc := bool_compose_assoc }

private instance instB : AxiomB Bool Unit :=
  { le := bool_le,
    lt := bool_lt,
    le_refl := bool_le_refl,
    le_trans := bool_le_trans,
    le_antisymm := bool_le_antisymm,
    lt_iff_le_not_le := bool_lt_iff,
    localFinite_past := bool_localFinite_past,
    localFinite_future := bool_localFinite_future,
    weaving_axiom := bool_weaving_axiom }

private instance instD : AxiomD Bool Unit :=
  { op_weaving := bool_op_weaving }

private instance instC : AxiomC Bool Unit :=
  { amplitude := bool_amplitude,
    norm_one := bool_amplitude_norm_one,
    comp_rule := bool_amplitude_comp,
    amplitude_injective := bool_amplitude_injective }

private instance instF : AxiomF Bool Unit :=
  { scale := bool_scale,
    scale_pos := bool_scale_pos,
    scale_limit := bool_scale_limit }

private instance instG : AxiomG Bool Unit :=
  { spin_network := Unit,
    amplitude_spin := fun (_ : Unit) => (1 : ℂ) }

private instance instH : AxiomH Bool Unit :=
  { gauge_group := Unit,
    field_content := bool_field_content,
    lagrangian := bool_lagrangian }

private instance instI : @AxiomI Bool Unit instA instB :=
  { entropy := bool_entropy,
    entropy_nonneg := bool_entropy_nonneg,
    entropy_subadditive := bool_entropy_subadditive,
    information_causal := bool_information_causal }

private instance instJ : AxiomJ Bool Unit :=
  { evolve := bool_evolve,
    causal_update := bool_causal_update,
    comp_evolve := bool_comp_evolve }

end boolModel

/-- Bool 模型 (boolModel) -/
def boolModel : Theory Bool Unit :=
  { toAxiomA := boolModel.instA,
    toAxiomB := boolModel.instB,
    toAxiomD := boolModel.instD,
    toAxiomC := boolModel.instC,
    toAxiomF := boolModel.instF,
    toAxiomG := boolModel.instG,
    toAxiomH := boolModel.instH,
    toAxiomI := boolModel.instI,
    toAxiomJ := boolModel.instJ }

/-! ============================================================================
   一致性定理：理论存在非空模型
   ============================================================================ -/

theorem trivialModel_exists : Nonempty (Theory Unit Unit) :=
  ⟨trivialModel⟩

theorem boolModel_exists : Nonempty (Theory Bool Unit) :=
  ⟨boolModel⟩

/-- CSQIT 理论是一致的：存在至少一个模型 -/
theorem csqit_theory_consistent : ∃ (M C : Type), Nonempty (Theory M C) :=
  ⟨Unit, Unit, trivialModel_exists⟩

end CSQIT
