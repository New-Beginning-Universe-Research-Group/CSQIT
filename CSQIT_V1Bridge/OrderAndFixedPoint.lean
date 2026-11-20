/-
================================================================================
CSQIT_V1Bridge — 第一代（V1.0 → V7.1.1）与 v23 的接口检验
模块: CSQIT_V1Bridge.OrderAndFixedPoint
版本: v0.2.0（2026-11-07）
================================================================================

本模块只做两件事，均为否定性结论（no-go），不新增任何公设：

  §1 因果序：
      V1 A3 要求操作上有偏序 ≺ 且 f ≺ f∘g。v23 的 CompilerAxiom 五字段
      不含任何序关系。这里证明：不存在一个只依赖五字段的函数 ord，
      使它在**每个** CompilerAxiom 模型上都是与 compose 相容的严格偏序。
      反例模型是左投影 compose α β := α。

      同时给出一个条件性构造（W2）：在无右单位元的模型上，
      α ≺ β := ∃ γ, β = α∘γ ∧ β ≠ α 确实是严格偏序且与 compose 相容。

  §2 自指不动点：
      V1.0 A3 / Nature S4.2 断言自指方程有解（Banach）。v23 只证了
      「若存在则唯一」（AxiomDerivation.lean 的 weave_fixed_point_unique）。
      这里用一个合法的 AxiomA 模型（compose α β := α+β+1）证明存在性
      不是 AxiomA 的推论；再给出一个存在不动点的模型，说明该性质是
      模型依赖的，而不是可导的公理后果。
      另给同一反例在**极简五字段** `CompilerAxiom` 上的版本，直接对应
      「存在性在现有五字段下不可导出」。

纪律：零新增 axiom、零 sorry；只 import 既有模块；
      不修改 CSQIT_W1 / CSQIT_Enhanced 的任何文件。
================================================================================ -/

import CSQIT_W1.CompilerAxioms
import CSQIT_W1.Foundation

namespace CSQIT_V1Bridge

open CSQIT_W1.CompilerAxioms
open CSQIT_W1.Foundation

/-! ============================================================================
    §1. 因果序：no-go 与条件构造
   ============================================================================ -/

/-- 「与组合相容的严格偏序」：反自反 + 传递 + 对任意 α β 有 α ≺ α∘β。
    这是 V1 A3 在 v23 语言中的最小翻译。 -/
structure CompatibleStrictOrder {M C : Type*} (CA : CompilerAxiom M C)
    (r : C → C → Prop) : Prop where
  irrefl : ∀ x : C, ¬ r x x
  trans : ∀ x y z : C, r x y → r y z → r x z
  compat : ∀ α β : C, r α (CA.compose α β)

/-- 左投影模型：`compose α β := α`。五字段全部成立。
    它没有任何与组合相容的严格偏序（因为取 β 任意即得 α ≺ α）。 -/
@[reducible]
def leftProjection : CompilerAxiom ℕ ℕ where
  compose := fun a _ => a
  assoc := by
    intro a b c
    rfl
  input := fun _ => []
  compose_input := by
    intro a b
    simp
  input_nodup := by
    intro a
    simp

/-- **否定定理（W1）**：不存在只依赖 `CompilerAxiom` 五字段的 `ord`，
    使它在每个模型上都给出与 `compose` 相容的严格偏序。

    证明：把假设的 `ord` 作用到 `leftProjection`，取 α = β = 0；
    相容性给出 `ord leftProjection 0 0`，反自反性给出其否定。 -/
theorem no_uniform_compatible_order :
    ¬ ∃ ord : CompilerAxiom ℕ ℕ → ℕ → ℕ → Prop,
        ∀ CA, CompatibleStrictOrder CA (ord CA) := by
  rintro ⟨ord, h⟩
  have hord : ord leftProjection 0 0 := by
    have hc := (h leftProjection).compat 0 0
    simpa using hc
  exact (h leftProjection).irrefl 0 hord

/-- **条件构造（W2）**：若模型没有右单位元（`∀ x y, x∘y ≠ x`），
    则 `α ≺ β := ∃ γ, β = α∘γ ∧ β ≠ α` 是严格偏序且与组合相容。

    注意：`h` 是模型类假设，不是新公设；左投影模型违反它，
    而 `ℕ_{>0}` 上的加法满足它。 -/
theorem conditional_order {M C : Type*} [CA : CompilerAxiom M C]
    (h : ∀ x y : C, CA.compose x y ≠ x) :
    CompatibleStrictOrder CA (fun x y => ∃ z : C, y = CA.compose x z ∧ y ≠ x) := by
  refine { irrefl := ?_, trans := ?_, compat := ?_ }
  · -- 反自反
    intro x hx
    rcases hx with ⟨z, _, hne⟩
    exact hne rfl
  · -- 传递
    intro x y w hxy hyw
    rcases hxy with ⟨z, hyz, _⟩
    rcases hyw with ⟨z', hwz', _⟩
    have hw' : w = CA.compose x (CA.compose z z') := by
      calc
        w = CA.compose y z' := hwz'
        _ = CA.compose (CA.compose x z) z' := by rw [← hyz]
        _ = CA.compose x (CA.compose z z') := CA.assoc x z z'
    refine ⟨CA.compose z z', hw', ?_⟩
    intro hwx
    have hx : CA.compose x (CA.compose z z') = x := by
      rw [← hw']
      exact hwx
    exact h x (CA.compose z z') hx
  · -- 与组合相容
    intro α β
    exact ⟨β, rfl, h α β⟩

/-! ============================================================================
    §2. 自指不动点：存在性不是公理后果
   ============================================================================ -/

/-- 反例模型：`compose α β := α + β + 1`。结合律成立，但
    `α∘α = α` 化为 `α + α + 1 = α`，在 `ℕ` 上无解。 -/
@[reducible]
def noFixModel : AxiomA ℕ ℕ where
  input := fun _ => []
  output := fun _ => 0
  input_nodup := by
    intro a
    simp
  compose := fun a b => a + b + 1
  compose_input := by
    intro a b
    simp
  compose_output := by
    intro a b
    simp
  compose_assoc := by
    intro a b c
    omega

/-- 存在模型：`compose α β := α + β`，不动点 α = 0。 -/
@[reducible]
def addModel : AxiomA ℕ ℕ where
  input := fun _ => []
  output := fun _ => 0
  input_nodup := by
    intro a
    simp
  compose := fun a b => a + b
  compose_input := by
    intro a b
    simp
  compose_output := by
    intro a b
    simp
  compose_assoc := by
    intro a b c
    omega

/-- **否定定理（W1）**：`AxiomA` 不保证自指不动点存在。
    即 `∀ A, ∃ α, A.compose α α = α` 不成立；V1.0 的 Banach 存在性
    不能由 v23 的代数公理推出（它还需要收缩 + 完备，属于新增公设）。 -/
theorem no_uniform_fixed_point :
    ¬ ∀ A : AxiomA ℕ ℕ, ∃ α : ℕ, A.compose α α = α := by
  intro h
  rcases h noFixModel with ⟨α, hα⟩
  have hα' : α + α + 1 = α := hα
  omega

/-- **独立性见证（W1）**：存在性在另一个合法模型中成立，
    因此「有/无不动点」是模型性质，不是 `AxiomA` 的定理。 -/
theorem fixed_point_exists_in_some_model :
    ∃ A : AxiomA ℕ ℕ, ∃ α : ℕ, A.compose α α = α := by
  refine ⟨addModel, 0, ?_⟩
  rfl

/- 同一结论在极简五字段 `CompilerAxiom` 上的版本。 -/

/-- 五字段反例模型：`noFixModel` 的 `compose`/`input` 分量。
    注意 `CompilerAxiom` 没有 `output`，故这里只填五个字段。 -/
@[reducible]
def noFixCA : CompilerAxiom ℕ ℕ where
  compose := fun a b => a + b + 1
  assoc := by
    intro a b c
    omega
  input := fun _ => []
  compose_input := by
    intro a b
    simp
  input_nodup := by
    intro a
    simp

/-- **G2（五字段版，W1）**：`CompilerAxiom` 的五个字段不保证自指不动点存在。
    即「存在 α 使 α∘α = α」不是五字段的推论；V1.0 的 Banach 存在性
    还需要收缩与完备，属于额外结构。 -/
theorem no_uniform_fixed_point_five :
    ¬ ∀ CA : CompilerAxiom ℕ ℕ, ∃ α : ℕ, CA.compose α α = α := by
  intro h
  rcases h noFixCA with ⟨α, hα⟩
  have hα' : α + α + 1 = α := hα
  omega

/-- **五字段独立性见证（W1）**：左投影模型上每个 `α` 都是不动点，
    故「有没有不动点」在五字段层面同样是模型性质。 -/
theorem fixed_point_exists_in_some_compiler :
    ∃ CA : CompilerAxiom ℕ ℕ, ∃ α : ℕ, CA.compose α α = α :=
  ⟨leftProjection, 0, rfl⟩

end CSQIT_V1Bridge
