/- ================================================================================
CSQIT — 「演化保振幅（酉性）」能不能推出来
文件: CSQIT_Enhanced/EvolutionFaithfulness.lean

结论（逐条对应任务 A/B 节，每条都挂本文件内的定理名）：

  A1  Foundation 层：CSQIT_V1Bridge/AmplitudeStructure.lean:57（右消去）、:69（左消去），
      前提仅 [AxiomA M C][AxiomC M C]，无额外假设。
      ' 层：库里既有文件没有 `A'.compose` 的消去定理，本文件补证
      amplitude_ne_zero' / compose_right_cancel' / compose_left_cancel'
      （前提仅 [AxiomA'][AxiomC']）。层次错配由此消除。

  A2  `evolve (compose α β) = evolve β ∘ evolve α`：见 evolve_comp_eq。
      需要 funext，**不是** rfl。

  A3  轨道忠实性按原陈述 **不成立**：见 orbit_faithful_fails。
      反例模型 U 同时满足 AxiomA' / AxiomB' / AxiomC' / AxiomJ'
      （振幅 false ↦ 1, true ↦ −1，在单位圆上且与 xor 相容），
      所以「反例模型里没有振幅」不能作为反驳。

  A4  A3 的正确补救（条件档）：把「`evolve : C → (M → M)` 单射」作为前提
      （记作 EvolveFaithful），则 A1 + A2 **确实能推出**轨道忠实性：
      orbit_faithful_of_evolve_faithful。
      这条前提推不出来：unitBool_evolve_not_injective（模型 U 中不成立）。
      只加「某 α 的 evolve 满射」不够：surjectivity_insufficient。

  A5  断裂点：轨道假设只给 `evolve β ∘ evolve α = evolve γ ∘ evolve α`；
      A2 把它等价改写为 `evolve (compose α β) = evolve (compose α γ)`；
      再往下走到 `compose α β = compose α γ` 必须 `evolve` 单射——这就是缺的那一条。
      无单射时反例里 compose 项明确不等：cancellation_route_blocked。

  B1  可陈述的最强「酉性」是 AxiomC'/AxiomC 的 norm_one，其类型里没有 M、没有 evolve，
      故对任何演化自动成立——即空洞成立：
      unitarity_has_no_state_argument / unitarity_has_no_state_argument'。

  B2  演化不被其余公理决定：evolve_not_determined（同一套 A'/B' 上挂
      `evolve ≡ id` 与 `evolve ≡ true` 两个 AxiomJ'）。
      常值演化把任何 `Bool → Bool` 不变量压成常数：
      const_evolve_yields_trivial_invariants。

层级：A 档（零新增 axiom、零 sorry；只用 Mathlib 与 CSQIT_Enhanced.Axioms）
证据链：AxiomC' : Axioms.lean:828；AxiomJ' : Axioms.lean:710；
        fin7/fin8 的 evolve 恒等：EnhancedModels.lean:452 / :568；
        natPartialModel 的 evolve = x + α：EnhancedModels.lean:1040（PartialTheory' 字段）。
================================================================================ -/

import CSQIT_Enhanced.Axioms
import Mathlib.Data.Set.Finite.Basic

namespace CSQIT_Enhanced.EvolutionFaithfulness

open CSQIT_Enhanced

/-! ============================================================================
   §A1  规则侧可消去：AxiomC' 层的补证
   ============================================================================ -/

/-- 振幅非零（由 `norm_one` 与 `normSq 0 = 0` 得到）。 -/
theorem amplitude_ne_zero' {M C : Type*} [A' : AxiomA' M C] [C' : AxiomC' M C]
    (α : C) : C'.amplitude α ≠ 0 := by
  intro h0
  have h1 := C'.norm_one α
  rw [h0] at h1
  simp at h1

/-- **A1-右**：`AxiomC'` ⇒ `A'.compose` 右消去。
    `α∘β = α∘γ ⟹ β = γ`。前提只有 `[AxiomA'][AxiomC']`。 -/
theorem compose_right_cancel' {M C : Type*} [A' : AxiomA' M C] [C' : AxiomC' M C]
    {α β γ : C} (h : A'.compose α β = A'.compose α γ) : β = γ := by
  have h' : C'.amplitude (A'.compose α β) = C'.amplitude (A'.compose α γ) := by
    rw [h]
  rw [C'.comp_rule, C'.comp_rule] at h'
  exact C'.amplitude_injective (mul_left_cancel₀ (M₀ := ℂ) (amplitude_ne_zero' α) h')

/-- **A1-左**：`AxiomC'` ⇒ `A'.compose` 左消去。
    `α∘β = γ∘β ⟹ α = γ`。 -/
theorem compose_left_cancel' {M C : Type*} [A' : AxiomA' M C] [C' : AxiomC' M C]
    {α β γ : C} (h : A'.compose α β = A'.compose γ β) : α = γ := by
  have h' : C'.amplitude (A'.compose α β) = C'.amplitude (A'.compose γ β) := by
    rw [h]
  rw [C'.comp_rule, C'.comp_rule] at h'
  exact C'.amplitude_injective (mul_right_cancel₀ (M₀ := ℂ) (amplitude_ne_zero' β) h')

/-! ============================================================================
   §A2  evolve 是反变的半群作用
   ============================================================================ -/

/-- **A2**：`evolve (compose α β) = evolve β ∘ evolve α`（先 α 后 β）。
    这是 `AxiomJ'.comp_evolve` 的 `Function.comp` 形式，**不是 rfl**：
    必须用 `funext` 把逐点等式升为函数等式。 -/
theorem evolve_comp_eq {M C : Type*} [A' : AxiomA' M C] [B' : AxiomB' M C]
    [J' : AxiomJ' M C] (α β : C) :
    J'.evolve (A'.compose α β) = (J'.evolve β) ∘ (J'.evolve α) := by
  funext x
  exact J'.comp_evolve α β x

/-! ============================================================================
   §A3  轨道忠实性：陈述、反例、以及能推出的条件版
   ============================================================================ -/

/-- **轨道忠实性（A3 的精确陈述）**：
    对规则 `α`，若 `evolve β` 与 `evolve γ` 在轨道 `Im(evolve α)` 上逐点一致，
    则 `β = γ`。 -/
def OrbitFaithful {M C : Type*} [A' : AxiomA' M C] [B' : AxiomB' M C]
    [J' : AxiomJ' M C] (α : C) : Prop :=
  ∀ β γ : C, (∀ x : M, J'.evolve β (J'.evolve α x) = J'.evolve γ (J'.evolve α x)) → β = γ

/-! ----------------------------------------------------------------------------
   反例模型 U：M = Unit，C = Bool，
     compose = xor，amplitude false = 1 / true = −1，
     evolve ≡ ()（与 α、x 都无关）。
   四个公理 A' / B' / C' / J' 全部满足，但 evolve 与规则无关，
   于是 A3 的假设恒真而结论可假。
   ---------------------------------------------------------------------------- -/

/-- 反例模型 U 的 AxiomA'：`input ≡ []`，`output ≡ ()`，`compose = xor`。 -/
instance unitBoolAxiomA' : AxiomA' Unit Bool where
  input := fun _ => []
  output := fun _ => ()
  input_nodup := fun _ => by simp
  compose := Bool.xor
  combine := fun _ _ => ()
  combine_assoc := fun _ _ _ => rfl
  compose_input := fun _ _ => rfl
  compose_output' := fun _ _ => rfl
  compose_assoc := fun a b c => by cases a <;> cases b <;> cases c <;> rfl

/-- 反例模型 U 的 AxiomB'：`le ≡ True`，`lt ≡ False`（Unit 上唯一可能的序）。 -/
instance unitBoolAxiomB' : AxiomB' Unit Bool where
  le := fun _ _ => True
  lt := fun _ _ => False
  le_refl := fun _ => trivial
  le_trans := fun _ _ _ _ _ => trivial
  le_antisymm := fun x y _ _ => Subsingleton.elim x y
  lt_iff_le_not_le := fun _ _ => ⟨fun h => h.elim, fun h => h.2 trivial⟩
  localFinite_past := fun _ => Set.finite_empty
  localFinite_future := fun _ => Set.finite_empty
  weaving_axiom' := fun _ x hx => by cases hx

/-- 反例模型 U 的振幅：`false ↦ 1`，`true ↦ −1`。
    这两个值都在单位圆上，且与 `xor` 相容（`(−1)·(−1) = 1`）。 -/
def unitBoolAmplitude : Bool → ℂ
  | false => 1
  | true => -1

/-- 反例模型 U 的 AxiomC'：振幅单射、模方为 1、乘法律成立。
    这一实例的存在说明：A3 的反例**不是**靠「模型里没有振幅」得来的。 -/
instance unitBoolAxiomC' : AxiomC' Unit Bool where
  amplitude := unitBoolAmplitude
  norm_one := fun α => by
    cases α
    · show Complex.normSq (1 : ℂ) = 1
      norm_num [Complex.normSq_apply]
    · show Complex.normSq (-1 : ℂ) = 1
      norm_num [Complex.normSq_apply]
  comp_rule := fun α β => by
    cases α <;> cases β
    · show (1 : ℂ) = 1 * 1
      norm_num
    · show (-1 : ℂ) = 1 * (-1)
      norm_num
    · show (-1 : ℂ) = (-1) * 1
      norm_num
    · show (1 : ℂ) = (-1) * (-1)
      norm_num
  amplitude_injective := by
    intro a b h
    cases a <;> cases b
    · rfl
    · exfalso
      have h' := congrArg Complex.re h
      have h1 : (unitBoolAmplitude false).re = (1 : ℝ) := by simp [unitBoolAmplitude]
      have h2 : (unitBoolAmplitude true).re = (-1 : ℝ) := by simp [unitBoolAmplitude]
      rw [h1, h2] at h'
      have hc : (2 : ℝ) = 0 := by
        have := congrArg (fun t => t + 1) h'
        simpa using this
      exact two_ne_zero hc
    · exfalso
      have h' := congrArg Complex.re h
      have h1 : (unitBoolAmplitude true).re = (-1 : ℝ) := by simp [unitBoolAmplitude]
      have h2 : (unitBoolAmplitude false).re = (1 : ℝ) := by simp [unitBoolAmplitude]
      rw [h1, h2] at h'
      have hc : (2 : ℝ) = 0 := by
        have := congrArg (fun t => t + 1) h'
        simpa using this.symm
      exact two_ne_zero hc
    · rfl

/-- 反例模型 U 的 AxiomJ'：`evolve α x = ()`（常值，与 α、x 均无关）。 -/
instance unitBoolAxiomJ' : AxiomJ' Unit Bool where
  evolve := fun _ _ => ()
  causal_update := fun _ _ => trivial
  comp_evolve := fun _ _ _ => rfl

/-- **A3 不成立**：在模型 U 中取 `α = false`，`evolve false` 与 `evolve true`
    在轨道上逐点一致（两边恒为 `()`），但 `false ≠ true`。 -/
theorem orbit_faithful_fails :
    ¬ (∀ β γ : Bool,
        (∀ x : Unit, unitBoolAxiomJ'.evolve β (unitBoolAxiomJ'.evolve false x)
          = unitBoolAxiomJ'.evolve γ (unitBoolAxiomJ'.evolve false x)) → β = γ) := by
  intro h
  have hh : ∀ x : Unit,
      unitBoolAxiomJ'.evolve false (unitBoolAxiomJ'.evolve false x)
        = unitBoolAxiomJ'.evolve true (unitBoolAxiomJ'.evolve false x) :=
    fun _ => rfl
  exact Bool.noConfusion (h false true hh)

/-- **A4 的满射前提在反例模型中确实满足**：`evolve α : Unit → Unit` 满射。 -/
theorem unitBool_evolve_surjective (α : Bool) :
    Function.Surjective (unitBoolAxiomJ'.evolve α) := by
  intro y
  exact ⟨(), by cases y; rfl⟩

/-- **A4 不成立**：「存在满射的 `evolve α`」**不足以**得到轨道忠实性。
    模型 U 满足满射前提，但 `α = false` 处的轨道忠实性为假。 -/
theorem surjectivity_insufficient :
    (∀ α : Bool, Function.Surjective (unitBoolAxiomJ'.evolve α)) ∧
    ¬ (∀ β γ : Bool,
        (∀ x : Unit, unitBoolAxiomJ'.evolve β (unitBoolAxiomJ'.evolve false x)
          = unitBoolAxiomJ'.evolve γ (unitBoolAxiomJ'.evolve false x)) → β = γ) :=
  ⟨fun α => unitBool_evolve_surjective α, orbit_faithful_fails⟩

/-- **A5 断裂点**：轨道假设成立，而 A1 消去律所需的前提
    `compose α β = compose α γ` 在此处**为假**。
    A2 只把 `compose` 的相等送向 `evolve` 的相等，方向不可逆。 -/
theorem cancellation_route_blocked :
    (∀ x : Unit, unitBoolAxiomJ'.evolve false (unitBoolAxiomJ'.evolve false x)
        = unitBoolAxiomJ'.evolve true (unitBoolAxiomJ'.evolve false x))
      ∧ unitBoolAxiomA'.compose false false ≠ unitBoolAxiomA'.compose false true := by
  constructor
  · intro x
    rfl
  · show (false : Bool) ≠ true
    decide

/-- **真正的补救前提**：`evolve : C → (M → M)` 单射。
    这条性质被 `AxiomJ`/`AxiomJ'` 完全无视（两者只管 `comp_evolve` 与
    `causal_update`），必须作为额外前提显式加入。 -/
def EvolveFaithful {M C : Type*} [A' : AxiomA' M C] [B' : AxiomB' M C]
    [J' : AxiomJ' M C] : Prop :=
  ∀ β γ : C, (∀ x : M, J'.evolve β x = J'.evolve γ x) → β = γ

/-- **满射只能做到这一步**：若 `evolve α` 满射，则「在 `Im(evolve α)` 上一致」
    可以升为「在整个 M 上一致」——但得到的是 `evolve β = evolve γ`，
    **不是** `β = γ`。差的那一步恰好就是 `EvolveFaithful`。 -/
theorem evolve_eq_of_surjective {M C : Type*} [A' : AxiomA' M C] [B' : AxiomB' M C]
    [J' : AxiomJ' M C] {α β γ : C} (hsurj : Function.Surjective (J'.evolve α))
    (h : ∀ x : M, J'.evolve β (J'.evolve α x) = J'.evolve γ (J'.evolve α x)) :
    J'.evolve β = J'.evolve γ := by
  funext y
  obtain ⟨x, rfl⟩ := hsurj y
  exact h x

/-- **A4 的正确形式（条件档）——A1 + A2 + `EvolveFaithful` ⇒ A3**：
    1. 轨道假设 `∀ x, evolve β (evolve α x) = evolve γ (evolve α x)`
       即 `evolve β ∘ evolve α = evolve γ ∘ evolve α`；
    2. 由 A2（evolve_comp_eq）改写为 `evolve (compose α β) = evolve (compose α γ)`；
    3. 由 EvolveFaithful 得 `compose α β = compose α γ`；
    4. 由 A1（compose_right_cancel'，需要 AxiomC'）得 `β = γ`。

    这正是原链条缺的那一环：第 3 步。 -/
theorem orbit_faithful_of_evolve_faithful {M C : Type*} [A' : AxiomA' M C]
    [C' : AxiomC' M C] [B' : AxiomB' M C] [J' : AxiomJ' M C]
    (h : EvolveFaithful (M := M) (C := C) (A' := A') (B' := B') (J' := J')) (α : C) :
    OrbitFaithful (M := M) (C := C) (A' := A') (B' := B') (J' := J') α := by
  intro β γ hβγ
  apply compose_right_cancel' (A' := A') (C' := C')
  apply h
  intro x
  have h1 : J'.evolve (A'.compose α β) x = J'.evolve β (J'.evolve α x) := by
    have := congrFun (evolve_comp_eq (α := α) (β := β)) x
    simpa [Function.comp_apply] using this
  have h2 : J'.evolve (A'.compose α γ) x = J'.evolve γ (J'.evolve α x) := by
    have := congrFun (evolve_comp_eq (α := α) (β := γ)) x
    simpa [Function.comp_apply] using this
  rw [h1, h2]
  exact hβγ x

/-- **`EvolveFaithful` 推不出来**：反例模型 U 中
    `evolve : Bool → (Unit → Unit)` 不单射（两个规则给出同一个常值函数）。
    因此 A3 若要有条件版，只能把这条前提显式写进定理。 -/
theorem unitBool_evolve_not_injective :
    ¬ Function.Injective (fun α : Bool => unitBoolAxiomJ'.evolve α) := by
  intro h
  have hh : (fun α : Bool => unitBoolAxiomJ'.evolve α) false
      = (fun α : Bool => unitBoolAxiomJ'.evolve α) true := by
    funext x
    rfl
  exact Bool.noConfusion (h hh)

/-! ============================================================================
   §B1  「酉性」在当前语言里只剩空洞形式
   ============================================================================ -/

/-- **B1**：可陈述的最强「酉性」是 `AxiomC.norm_one`。
    注意它的类型里**没有 M、没有 evolve**——正因为如此，它对任何演化都自动成立，
    即「在 evolve 下不变」是空洞的：不是推出来的，而是命题里根本没有状态。 -/
theorem unitarity_has_no_state_argument {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (α : C) : Complex.normSq (Cx.amplitude α) = 1 :=
  Cx.norm_one α

/-- **B1'**：同一事实在 `AxiomC'` 层的版本（供 A'/J' 层直接引用）。 -/
theorem unitarity_has_no_state_argument' {M C : Type*} [A' : AxiomA' M C] [C' : AxiomC' M C]
    (α : C) : Complex.normSq (C'.amplitude α) = 1 :=
  C'.norm_one α

/-! ============================================================================
   §B2  规则侧数据相同、evolve 不同：演化不被其余公理决定
   ============================================================================ -/

/-- 模型 B 的 AxiomA'：M = C = Bool，`input ≡ []`，`output ≡ false`，`compose = xor`，
    `combine a _ = a`。 -/
instance boolBoolAxiomA' : AxiomA' Bool Bool where
  input := fun _ => []
  output := fun _ => false
  input_nodup := fun _ => by simp
  compose := Bool.xor
  combine := fun a _ => a
  combine_assoc := fun _ _ _ => rfl
  compose_input := fun _ _ => rfl
  compose_output' := fun _ _ => rfl
  compose_assoc := fun a b c => by cases a <;> cases b <;> cases c <;> rfl

/-- 模型 B 的 AxiomB'：`le a b := a = false ∨ b = true`，`lt a b := a = false ∧ b = true`。 -/
instance boolBoolAxiomB' : AxiomB' Bool Bool where
  le := fun a b => a = false ∨ b = true
  lt := fun a b => a = false ∧ b = true
  le_refl := fun x => by cases x <;> simp
  le_trans := fun x y z h1 h2 => by cases x <;> cases y <;> cases z <;> simp_all
  le_antisymm := fun x y h1 h2 => by cases x <;> cases y <;> simp_all
  lt_iff_le_not_le := fun x y => by cases x <;> cases y <;> simp
  localFinite_past := fun x => by
    cases x
    · simpa using (Set.finite_empty : Set.Finite (∅ : Set Bool))
    · simpa using (Set.finite_singleton false : Set.Finite ({false} : Set Bool))
  localFinite_future := fun x => by
    cases x
    · simpa using (Set.finite_singleton true : Set.Finite ({true} : Set Bool))
    · simpa using (Set.finite_empty : Set.Finite (∅ : Set Bool))
  weaving_axiom' := fun _ x hx => by cases hx

/-- 模型 B 上的第一个演化：恒等。 -/
@[reducible] def boolEvolveId : AxiomJ' Bool Bool where
  evolve := fun _ x => x
  causal_update := fun _ x => by
    cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  comp_evolve := fun _ _ _ => rfl

/-- 模型 B 上的第二个演化：常值 `true`。 -/
@[reducible] def boolEvolveConst : AxiomJ' Bool Bool where
  evolve := fun _ _ => true
  causal_update := fun _ x => by
    cases x
    · exact Or.inl rfl
    · exact Or.inr rfl
  comp_evolve := fun _ _ _ => rfl

/-- `boolEvolveId` 的 evolve 逐点等于恒等（rfl）。 -/
theorem boolEvolveId_apply (α x : Bool) :
    @AxiomJ'.evolve Bool Bool boolBoolAxiomA' boolBoolAxiomB' boolEvolveId α x = x := rfl

/-- `boolEvolveConst` 的 evolve 逐点等于常值 `true`（rfl）。 -/
theorem boolEvolveConst_apply (α x : Bool) :
    @AxiomJ'.evolve Bool Bool boolBoolAxiomA' boolBoolAxiomB' boolEvolveConst α x = true := rfl

/-- **B2**：在**同一套** `AxiomA'`、`AxiomB'` 数据上，两个 `AxiomJ'` 结构的 `evolve`
    不同。故「演化」不被其余公理决定；要谈「保某种量」必须先给 M 装备该量。 -/
theorem evolve_not_determined :
    (@AxiomJ'.evolve Bool Bool boolBoolAxiomA' boolBoolAxiomB' boolEvolveId
      : Bool → Bool → Bool)
      ≠ @AxiomJ'.evolve Bool Bool boolBoolAxiomA' boolBoolAxiomB' boolEvolveConst := by
  intro h
  have h' := congrFun (congrFun h true) false
  rw [boolEvolveId_apply, boolEvolveConst_apply] at h'
  exact Bool.noConfusion h'

/-- **B2-补**：常值演化把任何 `Bool → Bool` 不变量压成常数——
    即在这类模型上「M 上的不变量」只有平凡（常值）的。
    形式地：若 `f` 在 `boolEvolveConst` 下不变，则 `f` 必为常函数。 -/
theorem const_evolve_yields_trivial_invariants (f : Bool → Bool)
    (hf : ∀ (α x : Bool),
      f (@AxiomJ'.evolve Bool Bool boolBoolAxiomA' boolBoolAxiomB' boolEvolveConst α x) = f x)
    (x y : Bool) : f x = f y := by
  have hx : f true = f x := by
    have h := hf true x
    rwa [boolEvolveConst_apply] at h
  have hy : f true = f y := by
    have h := hf true y
    rwa [boolEvolveConst_apply] at h
  rw [← hx, ← hy]

end CSQIT_Enhanced.EvolutionFaithfulness
