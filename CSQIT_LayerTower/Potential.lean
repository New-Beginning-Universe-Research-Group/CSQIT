/-
================================================================================
CSQIT-LayerTower · Potential
模块: CSQIT_LayerTower.Potential
把“引力 = 加性势”做成不绑定载体的 C 档公设接口，并精确划出
“字段不决定势值”的边界。

纪律：零新增 `axiom`、零 `sorry`；不改 CSQIT_W1 / CSQIT_Enhanced / CSQIT_V1Bridge。

档位：
  · B 档：`AdditivePotential`（新增定义）及其全部结构定理（机检）。
  · C 档：`AdditivePotential` 的**非零性**作为公设；本文件只给接口与非零见证，
          不给“这就是引力”的语义定理。
  · A 档：无（势结构在 `AxiomA` / `AxiomC` 字段里完全不存在）。

缺口（如实写出，不兜底）：
  · `AxiomA` 七字段（input/output/input_nodup/compose/compose_input/
    compose_output/compose_assoc）与 `AxiomC` 四字段（amplitude/norm_one/
    comp_rule/amplitude_injective）**都没有**势、度规、曲率字段；
  · 因此“势”只能是独立附加数据。`zero` 证明“存在加性势”恒真（不增加内容），
    真正有内容的是**非零势**（公设），且其数值不被任何字段决定
    （`witness_potential_not_determined_by_fields`）。
================================================================================ -/

import CSQIT_LayerTower.Tower
import CSQIT_V1Bridge.LayerWitness

namespace CSQIT_LayerTower

open CSQIT_W1.Foundation

noncomputable section

/-! ============================================================================
   §1. 参数化接口（B 档）
   ============================================================================ -/

/-- **C 档公设接口（参数化）**：任意 `AxiomA` 模型上的加性势。

    只依赖 `compose`，不依赖 `AxiomC` 的振幅字段——因此“势”与
    “相位/振幅”在结构上相互独立。 -/
structure AdditivePotential (M C : Type*) [A : AxiomA M C] where
  /-- 势函数（定义在载体 `C` 上，取实值） -/
  potential : C → ℝ
  /-- 公设核心：势在 `compose` 下可加 -/
  additive : ∀ a b : C, potential (A.compose a b) = potential a + potential b

namespace AdditivePotential

variable {M C : Type*} [A : AxiomA M C]

/-- **B 档**：零势。对**任意**模型都存在——所以“存在加性势”本身
    不增加任何内容；内容全在“存在非零势”这条 C 档公设上。 -/
def zero : AdditivePotential M C where
  potential := fun _ => 0
  additive := by
    intro a b
    simp

/-- **B 档**：缩放 `c • P` 仍是可加势。势空间是 `ℝ`-锥，
    不是仿射空间（加常数一般破坏可加性）。 -/
def scale (c : ℝ) (P : AdditivePotential M C) : AdditivePotential M C where
  potential := fun x => c * P.potential x
  additive := by
    intro a b
    rw [P.additive a b]
    ring

@[simp] theorem zero_potential (x : C) :
    (zero (M := M) (C := C)).potential x = 0 := rfl

theorem scale_potential (c : ℝ) (P : AdditivePotential M C) (x : C) :
    (scale c P).potential x = c * P.potential x := rfl

/-- **B 档**：加性势的外延性——`potential` 相同则势相同（`additive` 是命题）。 -/
theorem ext {P Q : AdditivePotential M C} (h : P.potential = Q.potential) : P = Q := by
  cases P with
  | mk p hp =>
    cases Q with
    | mk q hq =>
      have hpq : p = q := h
      subst hpq
      rw [Subsingleton.elim hp hq]

/-- **B 档**：零势的非零缩仍是零势（势的“零点”不因缩放而移动）。 -/
theorem scale_zero_eq_zero (c : ℝ) :
    (scale c (zero (M := M) (C := C))).potential = fun _ => 0 := by
  funext x
  rw [scale_potential]
  simp

end AdditivePotential

/-! ============================================================================
   §2. 势由“生成集上的初值”决定（B 档，可复用）
   ============================================================================ -/

/-- `S` 在 `compose` 下生成的闭包。势的初值只能落在这类表达式上。 -/
inductive Gen {M C : Type*} [A : AxiomA M C] (S : Set C) : C → Prop
  | base {x : C} (hx : x ∈ S) : Gen S x
  | step {a b : C} : Gen S a → Gen S b → Gen S (A.compose a b)

/-- **B 档（可复用）**：若整个载体都由 `S` 生成，则两个加性势只要在 `S` 上
    相同就恒等。这条说明势的数值**来自初值**，不是由 `AxiomA` 字段算出的。 -/
theorem additivePotential_eq_of_generates {M C : Type*} [A : AxiomA M C]
    {S : Set C} (hgen : ∀ x : C, Gen (A := A) S x)
    (P Q : AdditivePotential M C)
    (h : ∀ x ∈ S, P.potential x = Q.potential x) :
    ∀ x : C, P.potential x = Q.potential x := by
  intro x
  induction hgen x with
  | base hx => exact h _ hx
  | step ha hb iha ihb =>
      rw [P.additive, Q.additive, iha, ihb]

/-! ============================================================================
   §3. 见证模型：自由度恰为一个实数（B 档）
   ============================================================================ -/

/-- 见证模型（`a∘b = a+b+1`）上的单参数可加势：`n ↦ (n+1)·c`。 -/
def witnessPotential (c : ℝ) : @AdditivePotential ℕ ℕ CSQIT_V1Bridge.witnessAxiomA where
  potential := fun n => ((n : ℝ) + 1) * c
  additive := by
    intro a b
    show (((a + b + 1 : ℕ) : ℝ) + 1) * c
      = (((a : ℝ) + 1) * c + ((b : ℝ) + 1) * c)
    push_cast
    ring

theorem witnessPotential_zero (c : ℝ) : (witnessPotential c).potential 0 = c := by
  show (((0 : ℕ) : ℝ) + 1) * c = c
  norm_num

/-- **B 档**：见证塔顶（载体 `ℕ`）上，任何可加势都被 `potential 0` 完全决定。
    证明了什么：加性翻译下势没有额外结构。
    不证明什么：`potential 0` 的取值（那是初值，见 §4 的边界定理）。 -/
theorem witness_additivePotential_eq
    (P : @AdditivePotential ℕ ℕ CSQIT_V1Bridge.witnessAxiomA) (n : ℕ) :
    P.potential n = ((n : ℝ) + 1) * P.potential 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hstep : P.potential (k + 1) = P.potential k + P.potential 0 := by
        simpa using P.additive k 0
      rw [hstep, ih]
      push_cast
      ring

/-- **B 档**：势空间 ≅ `ℝ`——对每个实数 `c`，恰有一个可加势其
    `potential 0 = c`。自由度恰为一，且这个数是**初值**而非字段的函数。 -/
theorem witness_additivePotential_unique (c : ℝ) :
    ∃! P : @AdditivePotential ℕ ℕ CSQIT_V1Bridge.witnessAxiomA, P.potential 0 = c := by
  refine ⟨witnessPotential c, witnessPotential_zero c, ?_⟩
  intro Q hQ
  have hp : Q.potential = (witnessPotential c).potential := by
    funext n
    rw [witness_additivePotential_eq Q n, hQ]
    simp [witnessPotential]
  exact AdditivePotential.ext hp

/-- **B 档**：见证模型上至少有两个不同的可加势
    （`c = 0` 与 `c = 1`），因此势的数值不是模型唯一的。 -/
theorem witness_additivePotential_not_unique :
    ∃ P Q : @AdditivePotential ℕ ℕ CSQIT_V1Bridge.witnessAxiomA, P ≠ Q := by
  refine ⟨witnessPotential 0, witnessPotential 1, ?_⟩
  intro h
  have h0 : (witnessPotential 0).potential 0 = (witnessPotential 1).potential 0 :=
    congrArg (fun P : @AdditivePotential ℕ ℕ CSQIT_V1Bridge.witnessAxiomA =>
      P.potential 0) h
  rw [witnessPotential_zero 0, witnessPotential_zero 1] at h0
  exact absurd h0 (by norm_num)

/-- **B 档（非零见证）**：见证模型上存在非零可加势。
    这就是 C 档公设“存在非零加性势”的可满足性见证——它不证明该公设成立。 -/
theorem witness_additivePotential_nonzero :
    ∃ P : @AdditivePotential ℕ ℕ CSQIT_V1Bridge.witnessAxiomA, P.potential 0 ≠ 0 := by
  refine ⟨witnessPotential 1, ?_⟩
  rw [witnessPotential_zero 1]
  norm_num

/-! ============================================================================
   §4. `no_determiner` 边界：势值不是字段的函数（B 档）
   ============================================================================ -/

/-- **B 档（`no_determiner` 一族的势版本）**：不存在决定函数
    `f : AxiomA ℕ ℕ → (ℕ → ℝ)` 使 `f(字段) = 势`。

    证明方式与 `CSQIT_W1.IndependenceCheck.no_determiner` 相同：模型族内
    `AxiomA` 字段逐字相同（同一个 `witnessAxiomA`），而势值随参数 `c` 改变。

    这条是**边界**：任何“引力常数/势值被推导出来了”的说法，都与本定理冲突。 -/
theorem witness_potential_not_determined_by_fields :
    ¬ ∃ f : AxiomA ℕ ℕ → (ℕ → ℝ),
      ∀ c : ℝ, f CSQIT_V1Bridge.witnessAxiomA = fun n : ℕ => ((n : ℝ) + 1) * c := by
  rintro ⟨f, hf⟩
  have h0 : f CSQIT_V1Bridge.witnessAxiomA 0 = 0 := by
    have := congrFun (hf 0) 0
    simpa using this
  have h1 : f CSQIT_V1Bridge.witnessAxiomA 0 = 1 := by
    have := congrFun (hf 1) 0
    simpa using this
  linarith

/-! ============================================================================
   §5. 缺口的形式化证据：单点模型上一切加性势都是零势（B 档）

    “库里没有度规字段”不能直接写成一条 Lean 定理（不能量化“没有字段”），
    但它的**后果**可以：在最小的合法载体 `Unit` 上，字段对势的约束强到
    只剩零势——即使如此，字段也从未“给出”一个非零势值。 -/

instance unitAxiomA : AxiomA Unit Unit where
  input := fun _ => []
  output := fun _ => ()
  input_nodup := by
    intro _
    simp
  compose := fun _ _ => ()
  compose_input := by
    intro _ _
    simp
  compose_output := by
    intro _ _
    simp
  compose_assoc := by
    intro _ _ _
    rfl

/-- **B 档**：单点模型上，任何加性势取零。 -/
theorem unit_additivePotential_eq_zero (P : AdditivePotential Unit Unit) (x : Unit) :
    P.potential x = 0 := by
  have h : P.potential x = P.potential x + P.potential x := by
    simpa using P.additive x x
  linarith

/-- **B 档**：单点模型上的势恒为零函数（唯一性）。 -/
theorem unit_additivePotential_potential_eq_zero (P : AdditivePotential Unit Unit) :
    P.potential = fun _ => 0 :=
  funext (unit_additivePotential_eq_zero P)

end

end CSQIT_LayerTower
