/-
================================================================================
CSQIT_V1Bridge — 一般模型上的 AxiomC 空间：障碍定理 + 加法分类 + 空间双射
模块: CSQIT_V1Bridge.GeneralModelClassification
版本: v0.1.0（2026-11-07）
================================================================================

承接 `BOUNDARIES.md` §16（停在 G24–G25）。§16.4 新登记的未做项之一：
「一般模型上 AxiomC 分类——G24 只覆盖 witness compose」。本模块把分类
从单一模型推进到一般模型层：

  §1 一般障碍定理（G26，对**任意** AxiomA 模型成立，无载体限制）：
     · 幂等元必映到 1（乘法性 + 消去）；
     · 左/右吸收元 ⇒ AxiomC 空间为空（全部振幅被迫为 1，与单射矛盾）；
     · 两个不同幂等元 ⇒ AxiomC 空间为空；
     · 具体实例：左吸收模型（`compose a b = a`，即五字段 leftProjection
       的 AxiomA 版）上 AxiomC 空间为空。
  §2 加法模型完全分类（G27，`compose a b = a + b`）：
     · `amplitude n = (amplitude 1)^n`；注意与 witness 的差别：
       加法模型含幂等元 0，故 `amplitude 0 = 1` 被迫，参数点在 1 处；
     · 单射 ⟺ 参数非单位根；构造方向 `addPowAxiomC`；
     · 相等判据：⟺ 1 处振幅相等（数据无冗余）；
     · 作用量参数化 `S(n) = n • S(1)`；
     · 非空性：见证参数 `exp(iπ√2)` 给出具体成员。
  §3 分类空间双射（G28）：witness 与 add 两个 AxiomC 空间由「单点平移」
     `shift`（χ ↦ n ↦ χ(n+1)）与 `unshift`（ψ ↦ n ↦ ψ(0)^n）互为逆，
     故两空间同构；参数对应 `c_add = c_witness`。

结构含义（回答 §16.4 未做项「一般模型上 AxiomC 分类」的主体部分）：
  AxiomC 空间是**模型依赖**的，且已呈现清晰的三态结构：
    · 空空间（左吸收/含两个幂等元的模型）——结构无振幅层可言；
    · 单参数非空空间（witness、add）——整层 = 一个非单位根圆点的幂；
    · 两个非空空间在同参数意义下同构（G28）——「平移一层」不改变
      振幅层的本质内容。
  幂等元障碍（G26a）解释了 witness 与 add 的参数点差异：add 含幂等元
  0，振幅在 0 处被迫为 1，自由参数退到 1 处；witness 无幂等元，
  参数留在 0 处。

边界（不夸大）：
  1. 「一般分类」未完成：本模块给出一般**障碍**判据（空空间的三个
     充分条件）与两个规范非空模型的**完全分类**；任意 AxiomA 模型的
     AxiomC 空间的完整分类（含非吸收、非加法型模型）仍未做，不声称。
  2. G28 的双射只连接 witness 与 add 两个空间，不推广到任意模型对。
  3. 有限载体（如 ℤ/n）上 AxiomC 可非空（参数必为单位根）——与
     G7「层要求无限载体」形成对照；未形式化，登记为未做。

纪律：零新增 axiom、零 sorry；只 import 既有模块；
      不修改 CSQIT_W1 / CSQIT_Enhanced / 既有 V1Bridge 文件。
================================================================================ -/

import CSQIT_V1Bridge.AxiomCClassification

namespace CSQIT_V1Bridge

open CSQIT_W1.CompilerAxioms
open CSQIT_W1.Foundation
open Complex
open Real

/-! ============================================================================
    §0. 辅助：AxiomC 结构由振幅函数决定
   ============================================================================ -/

/-- 结构相等辅助（W1）：两个 `AxiomC` 的振幅函数相等 ⟹ 结构相等。
    其余三个字段是命题（`norm_one` / `comp_rule` / `amplitude_injective`），
    由证明无关性消去。G24d 的 `axiomC_eq_iff_zero_eq` 已在 witness 上
    隐式使用同一机制；此处提取为可复用引理。 -/
private theorem axiomC_ext {M C : Type*} {A : AxiomA M C} {x y : @AxiomC M C A}
    (h : x.amplitude = y.amplitude) : x = y := by
  cases x with
  | mk a₁ _ _ _ =>
    cases y with
    | mk a₂ _ _ _ =>
      have hproj : a₁ = a₂ := h
      cases hproj
      rfl

/-! ============================================================================
    §1. 一般障碍定理（G26）：幂等元与吸收元
   ============================================================================ -/

/-- **G26a（W1，A 档，一般障碍）**：任何 `AxiomC` 把幂等元送到 1。

    适用于**任意** `AxiomA` 模型、任意载体，无任何模型类假设。
    机制：`amplitude e = amplitude (e∘e) = amplitude e²`，非零消去。 -/
theorem amplitude_eq_one_of_idempotent {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    {e : C} (h : A.compose e e = e) : Cx.amplitude e = 1 := by
  have h1 : Cx.amplitude e = Cx.amplitude e * Cx.amplitude e := by
    have hr := Cx.comp_rule e e
    rwa [h] at hr
  have h2 : Cx.amplitude e * 1 = Cx.amplitude e * Cx.amplitude e := by
    rw [mul_one]; exact h1
  exact (mul_left_cancel₀ (amplitude_ne_zero e) h2).symm

/-- **G26b（W1，A 档）**：左单位元必映到 1（左单位元是幂等元）。 -/
theorem amplitude_eq_one_of_left_unit {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    {l : C} (h : ∀ b : C, A.compose l b = b) : Cx.amplitude l = 1 :=
  amplitude_eq_one_of_idempotent (e := l) (by rw [h l])

/-- **G26c（W1，A 档，空空间判据 I）**：存在左吸收元（`∃ a₀, ∀ b,
    compose a₀ b = a₀`）的非平凡载体上，`AxiomC` 空间为空。

    机制：`a₀` 处的乘法性迫使**所有**振幅为 1（消去 `amplitude a₀ ≠ 0`），
    与单射性在非平凡载体上直接矛盾。 -/
theorem no_axiomC_of_left_absorbing {M C : Type*} [A : AxiomA M C] [Nontrivial C]
    (h : ∃ a₀ : C, ∀ b : C, A.compose a₀ b = a₀) :
    ¬ Nonempty (@AxiomC M C A) := by
  rintro ⟨Cx⟩
  obtain ⟨a₀, ha₀⟩ := h
  have hall : ∀ b : C, Cx.amplitude b = 1 := by
    intro b
    have h1 : Cx.amplitude (A.compose a₀ b) = Cx.amplitude a₀ * Cx.amplitude b :=
      Cx.comp_rule a₀ b
    rw [ha₀ b] at h1
    have h2 : Cx.amplitude a₀ * 1 = Cx.amplitude a₀ * Cx.amplitude b := by
      rw [mul_one]; exact h1
    exact (mul_left_cancel₀ (amplitude_ne_zero a₀) h2).symm
  obtain ⟨x, y, hxy⟩ := Nontrivial.exists_pair_ne (α := C)
  exact hxy (Cx.amplitude_injective (by rw [hall x, hall y]))

/-- **G26d（W1，A 档，空空间判据 II）**：存在右吸收元（`∃ b₀, ∀ a,
    compose a b₀ = b₀`）的非平凡载体上，`AxiomC` 空间为空。机制对称。 -/
theorem no_axiomC_of_right_absorbing {M C : Type*} [A : AxiomA M C] [Nontrivial C]
    (h : ∃ b₀ : C, ∀ a : C, A.compose a b₀ = b₀) :
    ¬ Nonempty (@AxiomC M C A) := by
  rintro ⟨Cx⟩
  obtain ⟨b₀, hb₀⟩ := h
  have hall : ∀ a : C, Cx.amplitude a = 1 := by
    intro a
    have h1 : Cx.amplitude (A.compose a b₀) = Cx.amplitude a * Cx.amplitude b₀ :=
      Cx.comp_rule a b₀
    rw [hb₀ a] at h1
    have h2 : Cx.amplitude a * Cx.amplitude b₀ = 1 * Cx.amplitude b₀ := by
      rw [one_mul]; exact h1.symm
    exact mul_right_cancel₀ (amplitude_ne_zero b₀) h2
  obtain ⟨x, y, hxy⟩ := Nontrivial.exists_pair_ne (α := C)
  exact hxy (Cx.amplitude_injective (by rw [hall x, hall y]))

/-- **G26e（W1，A 档，空空间判据 III）**：两个不同幂等元 ⟹ `AxiomC`
    空间为空（两者都被 G26a 迫到 1，与单射矛盾）。 -/
theorem no_axiomC_of_two_idempotents {M C : Type*} [A : AxiomA M C] [Nontrivial C]
    (h : ∃ e₁ e₂ : C, e₁ ≠ e₂ ∧ A.compose e₁ e₁ = e₁ ∧ A.compose e₂ e₂ = e₂) :
    ¬ Nonempty (@AxiomC M C A) := by
  rintro ⟨Cx⟩
  obtain ⟨e₁, e₂, hne, h₁, h₂⟩ := h
  have h1 : Cx.amplitude e₁ = 1 := amplitude_eq_one_of_idempotent h₁
  have h2 : Cx.amplitude e₂ = 1 := amplitude_eq_one_of_idempotent h₂
  exact hne (Cx.amplitude_injective (by rw [h1, h2]))

/-! ============================================================================
    §1.5 具体实例：左吸收模型的 AxiomC 空间为空
   ============================================================================ -/

/-- 左吸收模型的 `AxiomA` 版：`compose a b = a`。五字段版 `leftProjection`
    已在 `OrderAndFixedPoint` 中给出（`AxiomC` 依赖 `AxiomA`，故此处补
    AxiomA 版）。声明为 `@[reducible]` def 而非 instance：可被 rfl 展开
    （`@[implicit_reducible]` 在 default 透明度下不展开，不行），同时
    不污染 ℕ ℕ 上的实例解析。 -/
@[reducible]
def leftAbsorbingAxiomA : AxiomA ℕ ℕ where
  input := fun _ => []
  output := fun _ => 0
  input_nodup := by
    intro _
    simp
  compose := fun a _ => a
  compose_input := by
    intro _ _
    simp
  compose_output := by
    intro _ _
    simp
  compose_assoc := by
    intro a b c
    rfl

/-- **G26f（W1，A 档，具体空空间）**：左吸收模型上 `AxiomC` 空间为空。

    与 witness / add（非空、单参数）形成三态对照的「空」态：
    AxiomC 空间是模型依赖的，且可以为空。 -/
theorem no_axiomC_leftAbsorbing : ¬ Nonempty (@AxiomC ℕ ℕ leftAbsorbingAxiomA) :=
  no_axiomC_of_left_absorbing (A := leftAbsorbingAxiomA) ⟨0, fun _ => rfl⟩

/-! ============================================================================
    §2. 加法模型的完全分类（G27）：`compose a b = a + b`
   ============================================================================ -/

/-- **递归步（加法模型，W1）**：`amplitude (n+1) = amplitude n · amplitude 1`。
    （对照 witness 版的递归步：那里递归元是 0，这里是 1。） -/
theorem amplitude_succ_of_add {A : AxiomA ℕ ℕ}
    (hcomp : ∀ a b : ℕ, A.compose a b = a + b)
    (Cx : @AxiomC ℕ ℕ A) (n : ℕ) :
    Cx.amplitude (n + 1) = Cx.amplitude n * Cx.amplitude 1 := by
  have h : Cx.amplitude (A.compose n 1) = Cx.amplitude n * Cx.amplitude 1 :=
    Cx.comp_rule n 1
  rwa [hcomp n 1] at h

/-- **G27a（W1，A 档，分类主引理）**：加法模型上任何 `AxiomC` 的振幅
    `amplitude n = c^n`，其中 `c := amplitude 1`。

    **与 witness 的结构差别**：加法模型含幂等元 `0`（`0+0 = 0`），
    由 G26a `amplitude 0 = 1` 被迫——自由参数从 0 处退到 1 处；
    witness 无幂等元，参数留在 0 处。 -/
theorem amplitude_eq_pow_of_add {A : AxiomA ℕ ℕ}
    (hcomp : ∀ a b : ℕ, A.compose a b = a + b)
    (Cx : @AxiomC ℕ ℕ A) (n : ℕ) :
    Cx.amplitude n = Cx.amplitude 1 ^ n := by
  induction n with
  | zero =>
    -- 0 是幂等元：amplitude 0 = amplitude 0² → 消去 → 1 = c^0
    have h1 : Cx.amplitude (A.compose 0 0) = Cx.amplitude 0 * Cx.amplitude 0 :=
      Cx.comp_rule 0 0
    rw [hcomp 0 0] at h1
    have h2 : Cx.amplitude 0 * 1 = Cx.amplitude 0 * Cx.amplitude 0 := by
      rw [mul_one]; exact h1
    exact (mul_left_cancel₀ (amplitude_ne_zero 0) h2).symm.trans (pow_zero _).symm
  | succ n ih =>
    rw [amplitude_succ_of_add hcomp Cx n, ih]
    exact (pow_succ (Cx.amplitude 1) n).symm

/-- 幂函数 `n ↦ c^n` 的吸收引理（W1）：若 `c ≠ 0`、非单位根、`a ≤ b`、
    `c^a = c^b`，则 `a = b`。（对照 G24 的 `pow_eq_absorbs_le`：无 +1 平移。） -/
private lemma pow_eq_absorbs_le_zero {c : ℂ} (hc0 : c ≠ 0)
    (hnot : ¬ IsRootOfUnityC c) {a b : ℕ} (hle : a ≤ b)
    (h : c ^ a = c ^ b) : a = b := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  by_cases hk0 : k = 0
  · omega
  · exfalso
    have hexp : (b : ℕ) = a + k := hk
    subst hexp
    -- h : c ^ a = c ^ (a + k)
    have hpos : 0 < k := by omega
    rw [pow_add] at h
    -- h : c ^ a = c ^ a * c ^ k
    have hcancel : c ^ k = 1 := by
      have h3 : c ^ a * 1 = c ^ a * c ^ k := by rw [mul_one]; exact h
      exact (mul_left_cancel₀ (pow_ne_zero a hc0) h3).symm
    exact hnot ⟨k, hpos, hcancel⟩

/-- **G27b（W1，A 档，单射判据）**：`|c| = 1` 时 `n ↦ c^n` 单射
    ⟺ `c` 非单位根。（对照 G24b 的 `n ↦ c^(n+1)` 版。） -/
theorem injective_pow_zero_iff_not_root {c : ℂ} (hc : Complex.normSq c = 1) :
    Function.Injective (fun n : ℕ => c ^ n) ↔ ¬ IsRootOfUnityC c := by
  constructor
  · rintro hinj ⟨N, hNpos, hroot⟩
    have h0 : c ^ (0 : ℕ) = c ^ N := by rw [pow_zero, hroot]
    have hzero : (0 : ℕ) = N := hinj h0
    omega
  · intro hnot
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0] at hc
      simp at hc
    intro a b hab
    rcases le_total a b with hle | hle
    · exact pow_eq_absorbs_le_zero hc0 hnot hle hab
    · exact (pow_eq_absorbs_le_zero hc0 hnot hle hab.symm).symm

/-- **G27c（W1，A 档，构造方向）**：在任何 `compose a b = a + b` 的模型上，
    `|c| = 1` 且非单位根的 `c` 反向给出合法 `AxiomC`（广义签名：对任意
    加法型 `AxiomA` 模型成立，不限于 `addModel`）。

    声明为 def 而非 instance：避免在 `ℕ ℕ` 上再制造默认 `AxiomC`
    实例（与 `powAxiomC` / `altAxiomC` 同一纪律）。 -/
@[reducible]
noncomputable def addPowAxiomC {A : AxiomA ℕ ℕ}
    (hcomp : ∀ a b : ℕ, A.compose a b = a + b)
    (c : ℂ) (hc : Complex.normSq c = 1) (hroot : ¬ IsRootOfUnityC c) :
    @AxiomC ℕ ℕ A where
  amplitude := fun n => c ^ n
  norm_one := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Complex.normSq_mul, ih, hc]
      norm_num
  comp_rule := by
    intro a b
    show c ^ (A.compose a b) = c ^ a * c ^ b
    rw [hcomp a b]
    exact pow_add c a b
  amplitude_injective := (injective_pow_zero_iff_not_root hc).mpr hroot

/-- **G27d（W1，A 档，相等判据）**：加法模型上两个 `AxiomC` 相等
    ⟺ 它们在 1 处的振幅相等。振幅层数据无冗余：恰为一个圆上
    非单位根参数（对照 G24d 的 0 处判据）。 -/
theorem axiomC_add_eq_iff_one_eq (Cx₁ Cx₂ : @AxiomC ℕ ℕ addModel) :
    Cx₁ = Cx₂ ↔ Cx₁.amplitude 1 = Cx₂.amplitude 1 := by
  constructor
  · exact fun h => h ▸ rfl
  · intro h
    have hamp : Cx₁.amplitude = Cx₂.amplitude := by
      funext n
      rw [amplitude_eq_pow_of_add (A := addModel) (by intro a b; rfl) Cx₁ n,
          amplitude_eq_pow_of_add (A := addModel) (by intro a b; rfl) Cx₂ n, h]
    exact axiomC_ext hamp

/-- **G27e（W1，A 档，作用量参数化）**：`addPowAxiomC c` 的作用量是
    `S(1)` 的整数倍：`S(n) = n • S(1)`。（对照 G24e 的 `S(n) = (n+1) • S(0)`：
    平移一位，参数点从 0 换到 1。） -/
theorem actionPhase_addPowAxiomC_smul (c : ℂ) (hc : Complex.normSq c = 1)
    (hroot : ¬ IsRootOfUnityC c) (n : ℕ) :
    @actionPhase ℕ ℕ addModel (addPowAxiomC (A := addModel) (fun _ _ => rfl) c hc hroot) n =
      (n : ℕ) • (@actionPhase ℕ ℕ addModel
        (addPowAxiomC (A := addModel) (fun _ _ => rfl) c hc hroot) 1) := by
  induction n with
  | zero =>
    have h1 : @actionPhase ℕ ℕ addModel
        (addPowAxiomC (A := addModel) (fun _ _ => rfl) c hc hroot) 0
        = Real.Angle.coe (Complex.arg (c ^ (0 : ℕ))) := rfl
    rw [h1, pow_zero, Complex.arg_one, Real.Angle.coe_zero, zero_smul]
  | succ n ih =>
    have hstep : @actionPhase ℕ ℕ addModel
        (addPowAxiomC (A := addModel) (fun _ _ => rfl) c hc hroot) (n + 1)
        = @actionPhase ℕ ℕ addModel
            (addPowAxiomC (A := addModel) (fun _ _ => rfl) c hc hroot) n
          + @actionPhase ℕ ℕ addModel
            (addPowAxiomC (A := addModel) (fun _ _ => rfl) c hc hroot) 1 := by
      have hadd := @actionPhase_add ℕ ℕ addModel
        (addPowAxiomC (A := addModel) (fun _ _ => rfl) c hc hroot) n 1
      exact hadd
    have hsmul : ((n : ℕ) + 1) •
        (@actionPhase ℕ ℕ addModel
          (addPowAxiomC (A := addModel) (fun _ _ => rfl) c hc hroot) 1) =
        (n : ℕ) • (@actionPhase ℕ ℕ addModel
            (addPowAxiomC (A := addModel) (fun _ _ => rfl) c hc hroot) 1) +
          (@actionPhase ℕ ℕ addModel
            (addPowAxiomC (A := addModel) (fun _ _ => rfl) c hc hroot) 1) := by
      rw [add_smul, one_smul]
    rw [hstep, ih]
    exact hsmul.symm

/-- **G27f（W1，A 档，非空性）**：加法模型的 `AxiomC` 空间非空：
    见证参数 `exp(iπ√2)`（已证非单位根，G24f）给出具体成员。

    至此三态对照完整：空（G26f）/ 非空单参数（witness G24、add G27）。 -/
@[reducible]
noncomputable def addAxiomCOfWitness : @AxiomC ℕ ℕ addModel :=
  addPowAxiomC (A := addModel) (fun _ _ => rfl)
    (witnessAxiomC.amplitude 0) (witnessAxiomC.norm_one 0) witness_not_root

/-! ============================================================================
    §3. 分类空间双射（G28）：witness 空间 ≅ add 空间
   ============================================================================ -/

/-- **G28a（W1，A 档，平移映射 add → witness）**：加法模型上的 `AxiomC`
    经「单点平移」给出见证 compose 上的 `AxiomC`：`(shift χ)(n) = χ(n+1)`。

    实现为直接结构字面量（经分类定理，χ(n) = χ(1)^n，故平移后的振幅
    `n ↦ χ(1)^(n+1)` 自动满足乘法性与单射性）。 -/
@[reducible]
noncomputable def shiftAxiomC (Cx : @AxiomC ℕ ℕ addModel) : @AxiomC ℕ ℕ witnessAxiomA where
  amplitude := fun n => Cx.amplitude 1 ^ (n + 1)
  norm_one := by
    intro n
    have hn : Complex.normSq (Cx.amplitude 1) = 1 := Cx.norm_one 1
    induction n with
    | zero => simpa using hn
    | succ m ih =>
      rw [pow_succ, Complex.normSq_mul, ih, hn]
      norm_num
  comp_rule := by
    intro a b
    show Cx.amplitude 1 ^ ((a + b + 1 : ℕ) + 1)
      = Cx.amplitude 1 ^ (a + 1) * Cx.amplitude 1 ^ (b + 1)
    have hexp : (a + b + 1 : ℕ) + 1 = (a + 1) + (b + 1) := by omega
    rw [hexp, pow_add]
  amplitude_injective := by
    have hroot : ¬ IsRootOfUnityC (Cx.amplitude 1) := by
      rintro ⟨N, hNpos, hroot⟩
      have hampN : Cx.amplitude N = Cx.amplitude 0 := by
        rw [amplitude_eq_pow_of_add (A := addModel) (by intro a b; rfl) Cx N,
            amplitude_eq_pow_of_add (A := addModel) (by intro a b; rfl) Cx 0, hroot]
        simp
      have h0 : N = 0 := Cx.amplitude_injective hampN
      omega
    have hc : Complex.normSq (Cx.amplitude 1) = 1 := Cx.norm_one 1
    exact (injective_pow_iff_not_root hc).mpr hroot

/-- 平移映射的振幅公式（W1）：`(shift χ)(n) = χ(n+1)`。 -/
theorem shiftAxiomC_amplitude (Cx : @AxiomC ℕ ℕ addModel) (n : ℕ) :
    (shiftAxiomC Cx).amplitude n = Cx.amplitude (n + 1) := by
  show Cx.amplitude 1 ^ (n + 1) = Cx.amplitude (n + 1)
  rw [amplitude_eq_pow_of_add (A := addModel) (by intro a b; rfl) Cx (n + 1)]

/-- **G28b（W1，A 档，平移映射 witness → add）**：见证模型上的 `AxiomC` ψ
    给出加法模型上的 `AxiomC`：`(unshift ψ)(n) = ψ(0)^n`。

    注意这是 ψ(n) = ψ(0)^(n+1) 的「去平移」：G24a 保证 ψ(n) = ψ(0)^(n+1)，
    除以 ψ(0)（单位模，用幂直接实现）即得乘法性。

    实现注记：此处用显式 `@AxiomC.mk` 构造而非 `where` 语法糖——后者对
    class 结果类型会触发实例合成（`addModel` 非注册实例，合成器错拿
    `witnessAxiomA` 而失败）。 -/
@[reducible]
noncomputable def unshiftAxiomC (ψ : @AxiomC ℕ ℕ witnessAxiomA) : @AxiomC ℕ ℕ addModel :=
  @AxiomC.mk ℕ ℕ addModel (fun n => ψ.amplitude 0 ^ n)
    (by
      intro n
      show Complex.normSq (ψ.amplitude 0 ^ n) = 1
      have hn : Complex.normSq (ψ.amplitude 0) = 1 := ψ.norm_one 0
      induction n with
      | zero => simp
      | succ m ih =>
        rw [pow_succ, Complex.normSq_mul, ih, hn]
        norm_num)
    (by
      intro a b
      show ψ.amplitude 0 ^ (a + b) = ψ.amplitude 0 ^ a * ψ.amplitude 0 ^ b
      exact pow_add _ _ _)
    (by
      have hroot : ¬ IsRootOfUnityC (ψ.amplitude 0) := by
        rintro ⟨N, hNpos, hroot⟩
        have hampN : ψ.amplitude N = ψ.amplitude 0 := by
          rw [amplitude_eq_pow_of_witness_compose (A := witnessAxiomA) (by intro a b; rfl) ψ N,
              pow_succ, hroot]
          simp
        have h0 : N = 0 := ψ.amplitude_injective hampN
        omega
      have hc : Complex.normSq (ψ.amplitude 0) = 1 := ψ.norm_one 0
      exact (injective_pow_zero_iff_not_root hc).mpr hroot)

/-- 平移映射的振幅公式（W1）：`(unshift ψ)(n) = ψ(0)^n`。 -/
theorem unshiftAxiomC_amplitude (ψ : @AxiomC ℕ ℕ witnessAxiomA) (n : ℕ) :
    (unshiftAxiomC ψ).amplitude n = ψ.amplitude 0 ^ n := rfl

/-- **G28f（W1，A 档，参数对应）**：平移保持单点参数：
    `(shift χ).amplitude 0 = χ.amplitude 1` 且
    `(unshift ψ).amplitude 1 = ψ.amplitude 0`——两个空间的参数是
    **同一个** c，双射不改变 U(1) 相位数据。 -/
theorem shiftAxiomC_param (Cx : @AxiomC ℕ ℕ addModel) :
    (shiftAxiomC Cx).amplitude 0 = Cx.amplitude 1 := by
  rw [shiftAxiomC_amplitude, Nat.zero_add]

theorem unshiftAxiomC_param (ψ : @AxiomC ℕ ℕ witnessAxiomA) :
    (unshiftAxiomC ψ).amplitude 1 = ψ.amplitude 0 := by
  rw [unshiftAxiomC_amplitude, pow_one]

/-- **G28c（W1，A 档，往返 I）**：`unshift ∘ shift = id`（振幅函数层面）。

    `(unshift (shift χ))(n) = (shift χ)(0)^n = χ(1)^n = χ(n)`（G27a）。 -/
theorem unshift_shiftAxiomC (Cx : @AxiomC ℕ ℕ addModel) :
    (unshiftAxiomC (shiftAxiomC Cx)).amplitude = Cx.amplitude := by
  funext n
  have h1 : (unshiftAxiomC (shiftAxiomC Cx)).amplitude n
      = (shiftAxiomC Cx).amplitude 0 ^ n := unshiftAxiomC_amplitude _ n
  have h2 : (shiftAxiomC Cx).amplitude 0 = Cx.amplitude 1 := shiftAxiomC_param Cx
  have h3 : Cx.amplitude n = Cx.amplitude 1 ^ n :=
    amplitude_eq_pow_of_add (A := addModel) (by intro a b; rfl) Cx n
  rw [h1, h2, h3]

/-- **G28d（W1，A 档，往返 II）**：`shift ∘ unshift = id`（振幅函数层面）。

    `(shift (unshift ψ))(n) = (unshift ψ)(n+1) = ψ(0)^(n+1) = ψ(n)`（G24a）。 -/
theorem shift_unshiftAxiomC (ψ : @AxiomC ℕ ℕ witnessAxiomA) :
    (shiftAxiomC (unshiftAxiomC ψ)).amplitude = ψ.amplitude := by
  funext n
  have h1 : (shiftAxiomC (unshiftAxiomC ψ)).amplitude n
      = (unshiftAxiomC ψ).amplitude (n + 1) := shiftAxiomC_amplitude _ n
  have h2 : (unshiftAxiomC ψ).amplitude (n + 1) = ψ.amplitude 0 ^ (n + 1) :=
    unshiftAxiomC_amplitude ψ (n + 1)
  have h3 : ψ.amplitude n = ψ.amplitude 0 ^ (n + 1) :=
    amplitude_eq_pow_of_witness_compose (A := witnessAxiomA) (by intro a b; rfl) ψ n
  rw [h1, h2, h3]

/-- **G28e（W1，A 档，双射）**：平移映射 `shift : AxiomC(add) → AxiomC(witness)`
    是双射（逆为 `unshift`）。两个分类空间同构：同一参数 c 的两种求值
    （`c^n` 与 `c^(n+1)`），witness 与 add 的振幅层无本质差异。 -/
theorem axiomC_shift_bijective :
    Function.Bijective (fun Cx : @AxiomC ℕ ℕ addModel => shiftAxiomC Cx) := by
  constructor
  · intro x y hxy
    have hxy' : shiftAxiomC x = shiftAxiomC y := hxy
    have h1 := unshift_shiftAxiomC x
    have h2 := unshift_shiftAxiomC y
    rw [hxy'] at h1
    have hamp : x.amplitude = y.amplitude := by rw [← h1, ← h2]
    exact axiomC_ext hamp
  · intro ψ
    exact ⟨unshiftAxiomC ψ, axiomC_ext (shift_unshiftAxiomC ψ)⟩

/-! ============================================================================
    汇总：G26–G28 四档

  新增结论（全部 W1、零新增公设、零 sorry）：

    G26a  一般障碍：幂等元必映到 1（任意模型、任意载体）
    G26b  左单位元映到 1
    G26c  空空间判据 I：左吸收元 ⇒ AxiomC 空间为空（非平凡载体）
    G26d  空空间判据 II：右吸收元同理
    G26e  空空间判据 III：两个不同幂等元 ⇒ 空间为空
    G26f  具体空空间：左吸收模型（leftProjection 的 AxiomA 版）
    G27a  加法分类主引理：amplitude n = c^n（c := amplitude 1；0 处被迫为 1）
    G27b  单射判据：n ↦ c^n 单射 ⟺ c 非单位根
    G27c  构造方向：addPowAxiomC
    G27d  相等判据：⟺ 1 处振幅相等（数据无冗余）
    G27e  作用量参数化：S(n) = n • S(1)
    G27f  非空性：见证参数给出具体成员
    G28a  平移映射 add → witness（经分类实现）
    G28b  平移映射 witness → add
    G28c/d 往返：unshift ∘ shift = id、shift ∘ unshift = id
    G28e  双射：两个分类空间同构
    G28f  参数对应：同一 c，双射不改变 U(1) 数据

  档位：全部 A 档（在既有 AxiomA/AxiomC/addModel/witnessAxiomA 定义上
  直接陈述并机检；无新增定义型前提——leftAbsorbingAxiomA 是具体模型
  def，不是公设）。

  信息增益：
    1. G24 的分类从 witness 单模型推广为：一般**障碍**判据（G26）+
       第二个规范模型的**完全分类**（G27）+ 两空间**同构**（G28）。
    2. AxiomC 空间呈三态结构：空（左吸收/双幂等）/ 单参数非空
       （witness、add）/ 两非空空间同构（平移双射，参数不变）。
    3. 幂等元障碍（G26a）解释 witness 与 add 的参数点差异：
       add 含幂等元 0 → amplitude 0 = 1 被迫 → 参数退到 1 处；
       witness 无幂等元 → 参数留在 0 处。
    4. 对 §16.4 未做项「一般模型上 AxiomC 分类」：主体已闭合于
       「障碍判据 + 两个规范模型分类 + 同构」；任意模型的完整分类
       仍开放（如实登记，不降格）。

  边界（不夸大）：
    1. 任意 AxiomA 模型的 AxiomC 空间完整分类未做（如非吸收、非加法型）。
    2. G28 双射只连接 witness 与 add，不推广到任意模型对。
    3. 有限载体上 AxiomC 可非空（参数必为单位根，如 ℤ/n 的特征）——
       与 G7「层要求无限载体」对照；未形式化，登记为未做。
================================================================================ -/

end CSQIT_V1Bridge
