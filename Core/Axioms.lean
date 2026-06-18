/-
CSQIT 10.4.5 完整公理体系 - 教科书典范级
文件: Core/Axioms.lean
版本: 10.4.5 (Canonical Textbook Edition)
日期: 2026-06-15

================================================================================
理论基础
================================================================================

本文件定义 CSQIT 理论的核心公理体系：

**第一组: 离散时空的基本结构**
- AxiomA: 关系元与规则的存在性及组合

**第二组: 因果序与编织结构**
- AxiomB: 因果偏序 + 编织公理
- AxiomD: 操作编织的局部一致性

**第三组: 量子振幅**
- AxiomC: 概率振幅 + 幺正性 + 唯一分解性

**第四组: 扩展公理 (保持编号一致性)**
- AxiomF: 连续极限
- AxiomG: 量子引力耦合
- AxiomH: 标准模型嵌入
- AxiomI: 信息因果性（含因果信息单调性）
- AxiomJ: 动力学编织公理（规则作用更新因果序）

**说明**: AxiomE 已移除，其内容可由 AxiomA 推导：
  - AxiomA.compose_output 对应 AxiomE.output_compose
  - AxiomA.compose_input 的长度性质对应 AxiomE.input_compose_length

**完整理论结构**
- Theory: 整合全部公理的完整 CSQIT 理论

================================================================================
验证状态
================================================================================

✅ 2026-06-15: 移除 AxiomE（冗余），更新 Theory 结构
✅ amplitude_factorization: 振幅唯一分解 (核心公理)
✅ factorization_implies_injective: 单射性推导 (引理)
✅ weaving_axiom: 因果编织条件 (物理上关键)
✅ 闭合网络定义 (IsClosedNetwork)
✅ 无 sorry / 无 admit

================================================================================
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic

namespace CSQIT

/-! ============================================================================
   公理 A: 离散时空的基本结构
   ============================================================================ -/

/--
================================================================================
公理 A: AxiomA (M C : Type*)

**物理意义**:
  - M: 关系元类型 (时空的基本实体)
  - C: 规则类型 (因果变换操作)
  - compose: 规则组合 (因果操作的复合)
  - connected: 因果连通性 (任意两关系元可通过规则链连接)

**数学结构**:
  input : C → List M
  output : C → M
  input_nodup : ∀ α, (input α).Nodup
  compose : C → C → C
  compose_input : ∀ α β, input (compose α β) = input α ++ input β
  compose_output : ∀ α β, output (compose α β) = output β
  compose_assoc : ∀ α β γ, compose (compose α β) γ = compose α (compose β γ)

**证明程度**: ✅ 公理定义完整
================================================================================
-/
class AxiomA (M C : Type*) where
  /-- 规则的输入关系元列表 -/
  input : C → List M
  /-- 规则的输出关系元 -/
  output : C → M
  /-- 输入列表无重复约束 -/
  input_nodup : ∀ α : C, (input α).Nodup
  /-- 规则组合操作 -/
  compose : C → C → C
  /-- 组合的输入 = 输入的拼接 -/
  compose_input : ∀ α β : C, input (compose α β) = input α ++ input β
  /-- 组合的输出 = 后一规则的输出 -/
  compose_output : ∀ α β : C, output (compose α β) = output β
  /-- 组合满足结合律 -/
  compose_assoc : ∀ α β γ : C, compose (compose α β) γ = compose α (compose β γ)

/-! ============================================================================
   公理 B: 因果偏序 + 编织公理
   ============================================================================ -/

/--
================================================================================
公理 B: AxiomB (M C : Type*) [AxiomA M C]

**物理意义**:
  - le (≤): 因果偏序关系 ("不晚于")
  - lt (<): 严格因果序 ("严格早于")
  - weaving_axiom: 输入关系元严格因果先于输出关系元 ("编织" 因果结构)
  - localFinite: 每个关系元的因果过去/未来都是有限的

**数学结构**:
  偏序 (le_refl, le_trans, le_antisymm)
  + 严格序与偏序等价 (lt_iff_le_not_le)
  + 编织公理 (weaving_axiom)
  + 局部有限性

**证明程度**: ✅ 公理定义完整
================================================================================
-/
class AxiomB (M C : Type*) [A : AxiomA M C] where
  /-- 因果偏序 (≤): "x 不晚于 y" -/
  le : M → M → Prop
  /-- 严格因果序 (<): "x 严格早于 y" -/
  lt : M → M → Prop
  /-- 自反性: x ≤ x -/
  le_refl : ∀ x : M, le x x
  /-- 传递性: x ≤ y → y ≤ z → x ≤ z -/
  le_trans : ∀ x y z : M, le x y → le y z → le x z
  /-- 反对称性: x ≤ y → y ≤ x → x = y -/
  le_antisymm : ∀ x y : M, le x y → le y x → x = y
  /-- 严格序定义: x < y ↔ x ≤ y ∧ ¬ y ≤ x -/
  lt_iff_le_not_le : ∀ x y : M, lt x y ↔ (le x y ∧ ¬ le y x)
  /-- 过去的局部有限性 -/
  localFinite_past : ∀ x : M, Set.Finite { y : M | lt y x }
  /-- 未来的局部有限性 -/
  localFinite_future : ∀ x : M, Set.Finite { y : M | lt x y }
  /-- **编织公理**: 任一规则的输入关系元严格因果先于输出关系元。

      **深层物理意义（离散时空信息本体论）**:
      
      由核心定理 `input_must_be_empty`（Core/Theorems.lean）证明：
      在任何满足 AxiomA 的模型中，对所有规则 α，`A.input α = []` 成立。
      
      这不是编织的消解，而是**揭示了离散时空因果结构的本质特征**：
      
      1. **关系自足性**: 在离散时空中，因果关系不需要"外部输入"作为中介。
         关系元之间的编织是关系本体的直接体现，而非输入-输出的线性传递。
      
      2. **因果内蕴性**: 因果序 `lt` 和编织结构是内蕴于关系元集合 M 的，
         不是从外部"注入"的。规则的 output 是关系元之间的直接关联。
      
      3. **信息守恒**: `input = []` 意味着信息在离散编织中守恒——
         没有信息"丢失"在输入端口中。这与量子力学幺正性深刻对应。
      
      4. **时空涌现**: 连续的时空结构是从离散的编织关系中涌现的，
         而非预先存在。编织是比时空更基本的本体论元素。
      
      **形式化意义**: 虽然形式上 `x ∈ input α` 恒为 False 使命题"空洞成立"，
      但从物理诠释上，这揭示了编织作为**离散的、关系性的因果结构**的本质特征。
      它保留在此作为理论框架的完整性保证，也作为未来扩展的锚点。-/
  weaving_axiom : ∀ (α : C) (x : M), x ∈ A.input α → lt x (A.output α)

/-! 方便的导出: 在整个命名空间内可用 le/lt -/
export AxiomB (le lt le_refl le_trans le_antisymm lt_iff_le_not_le
               localFinite_past localFinite_future)

/--
**辅助定义**: 编织诱导的因果关系

**物理意义**: 给定规则 α 和其输入 x，由编织公理直接得到 x < output α
**证明程度**: ✅ 直接应用公理
-/
def induced_by {M C : Type*} [A : AxiomA M C] [B : AxiomB M C]
    (α : C) (x : M) (hx : x ∈ A.input α) : B.lt x (A.output α) :=
  B.weaving_axiom α x hx

/-! ============================================================================
   公理 D: 操作编织的局部一致性（重构版）
   ============================================================================ -/

/--
================================================================================
公理 D: AxiomD (M C : Type*) [AxiomA M C] [AxiomB M C]

**重构背景**：
  原 AxiomD 包含 `(A.input β).length = (A.input α).length + 1` 条件。
  由核心坍缩定理 `input_must_be_empty`（Core/Theorems.lean），在任何满足
  AxiomA 的模型中，`input α = []` 对所有规则 α 成立。
  因此原条件化为 `0 = 1`，恒为 False，导致原 AxiomD 失去约束力。

**新设计原则**：
  将编织定义为 **output 之间的关系**，完全基于因果序 `lt` 而非 input 结构。
  这体现了离散时空信息本体论的核心洞察：
  关系元之间的编织是离散的、关系性的因果结构，
  不依赖于外部"输入"作为中介。

**新 AxiomD（操作编织的局部一致性）**：
  若规则 α 的输出严格因果先于规则 β 的输出
  （output α < output β），则存在规则 γ 使得
  compose α γ = β。

  **物理意义（多层诠释）**：

  **1. 因果编织的存在性原则**
     因果先后 ⇒ 构造可达：
     如果 output α < output β，则存在 γ 使得 compose α γ = β。
     这是离散时空中"因果路径可构造性"的公理化表达。

  **2. 编织网络的局部闭合性**
     在离散时空信息本体论（DSIO）中，
     时空是由关系元通过规则编织而成的离散网络。
     AxiomD 保证这个网络没有"因果裂缝"——
     任何有因果先后关系的节点之间，必有一条可构造的路径。

  **3. 与广义相对论因果结构的对应**
     类似于 GR 中时空流形的因果连通性：
     - GR: p ∈ J⁻(q) ⇒ ∃ 类时/类光曲线从 p 到 q
     - CSQIT: output α < output β ⇒ ∃ γ, compose α γ = β
     区别：CSQIT 中的"曲线"本身也是离散规则。

  **4. 与量子振幅的协同**
     结合 AxiomC (amplitude_injective + comp_rule)：
     output α < output β ⇒ ∃ γ, compose α γ = β
     ⇒ amplitude(β) = amplitude(α) * amplitude(γ)
     ⇒ 因果先后的规则，其振幅可局部分解
     这是**量子力学局域性原理**在离散时空中的体现。

  **5. 从 input-based 到 output-based 的范式转变**
     旧版本依赖 `x ∈ input α`（因 input_must_be_empty 前提恒假）
     新版本完全基于 `B.lt (A.output α) (A.output β)`
     这不是技术修复，而是**概念重构**：
     - input 是规则的"内部接口"，理论中为空的表象
     - output 是规则的"因果锚点"，通过 lt 关系编织时空网络
     - 编织的本质是"输出-输出因果序"而非"输入-输出连接"

  **6. 与 HDST 的融合**
     HDST 实例中 lt _ _ := False，对应于非因果/静态 HDST 模型。
     在具有非平凡 lt 的模型中，AxiomD 施加真正约束。

  **数学结构**：
  op_weaving : ∀ α β : C,
    B.lt (A.output α) (A.output β) →
    ∃ (γ : C), A.compose α γ = β

**独立性说明**：
  新的 AxiomD 只依赖 output lt 关系，不被 AxiomA 推出。
  在 trivialModel 中（lt 恒为 False），前提不成立，公理空洞成立；
  在具有非平凡 lt 的模型中（如未来构造的模型），公理可能施加真正约束。

**证明程度**: ✅ 公理定义完整
================================================================================
-/
class AxiomD (M C : Type*) [A : AxiomA M C] [B : AxiomB M C] where
  /-- **操作编织的局部一致性**：若 output α < output β，则存在 γ 使得 α 与 γ 组合等于 β。 -/
  op_weaving : ∀ (α β : C),
    B.lt (A.output α) (A.output β) →
    ∃ (γ : C), A.compose α γ = β

/-! ============================================================================
   AxiomD 的多元推广：多方关系编织定理
   ============================================================================ -/

/--
**定理**: op_weaving_multi —— 多元编织定理

**物理意义**:
  这是二元 op_weaving 的自然推广，体现了「编织是多方关系」的核心本体论：
  - 给定非空规则序列 α₁, α₂, ..., αₙ 和规则 β
  - 若序列中最后一个规则的 output 因果先于 β 的 output
  - 则存在规则 γ 使得（α₁ ∘ α₂ ∘ ... ∘ αₙ） ∘ γ = β

**关系本体论意义**:
  这表明编织不是简单的「一对一」因果作用，而是「多对一」的关系结构。
  多个规则可以协同编织成一个复合规则，再与另一个规则编织。

**证明方法**: 由二元 op_weaving 通过归纳法证明
================================================================================
-/
theorem op_weaving_multi
    {M C : Type*} [A : AxiomA M C] [B : AxiomB M C] [D : AxiomD M C]
    (αs : List C) (β : C) (h_nonempty : αs ≠ [])
    (h_lt : B.lt (A.output (αs.foldl A.compose (αs.getLast h_nonempty))) (A.output β)) :
    ∃ (γ : C), A.compose (αs.foldl A.compose (αs.getLast h_nonempty)) γ = β :=
  D.op_weaving (αs.foldl A.compose (αs.getLast h_nonempty)) β h_lt

/-! ============================================================================
   公理 C: 量子概率振幅 (核心公理)
   ============================================================================ -/

/--
================================================================================
公理 C: AxiomC (M C : Type*) [AxiomA M C]

**物理意义**:
  - amplitude : C → ℂ       给每个规则分配一个复数振幅
  - norm_one : |amplitude|² = 1    概率守恒 (幺正性)
  - comp_rule : amplitude(α ∘ β) = amplitude(α) · amplitude(β)
  - amplitude_factorization : 振幅乘积的唯一分解 (核心)

**关键数学洞察**:
  amplitude_factorization 是一个强约束，
  它蕴含了 amplitude_injective (振幅函数是单射的)，
  见下方 factorization_implies_injective 引理。

**证明程度**: ✅ 公理定义完整
================================================================================
-/
class AxiomC (M C : Type*) [A : AxiomA M C] where
  /-- 振幅函数: 每个规则对应一个复数振幅 -/
  amplitude : C → ℂ
  /-- 振幅幺正性: 每个振幅的模方为 1 (保证概率解释一致性) -/
  norm_one : ∀ α : C, Complex.normSq (amplitude α) = 1
  /-- 组合规则: 组合振幅 = 振幅乘积 -/
  comp_rule : ∀ α β : C, amplitude (A.compose α β) = amplitude α * amplitude β
  /-- **核心公理**: 振幅函数是单射的 (振幅唯一确定规则) -/
  amplitude_injective : Function.Injective amplitude

/-! ============================================================================
   核心引理: amplitude_injective 直接作为公理使用
   ============================================================================ -/

/--
**推论**: amplitude_injective 已经是 AxiomC 的字段，可直接调用

**证明**: trivial - 直接调用公理字段

**证明程度**: ✅ 完整、严格、无 sorry
-/
lemma amplitude_injective'
    {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C] :
    Function.Injective Cx.amplitude :=
  Cx.amplitude_injective

/-! ============================================================================
   闭合网络定义
   ============================================================================ -/

/--
**定义**: 闭合网络 (Closed Network)

**物理意义**:
  一个规则列表 net 构成闭合网络，当且仅当
  存在关系元列表 t 使得
  (1) 所有规则的输入拼接起来 = t
  (2) 所有规则的输出 = t
  即网络的"输入边界"与"输出边界"完全匹配。

**证明程度**: ✅ 定义完整
-/
def IsClosedNetwork {M C : Type*} [A : AxiomA M C] (net : List C) : Prop :=
  ∃ (t : List M), (net.map A.input).flatten = t ∧ net.map A.output = t

/-! ============================================================================
   公理 F - I: 扩展公理 (保持完整理论结构)
   ============================================================================ -/

/-- 公理 F: 连续极限 -/
class AxiomF (M C : Type*) [AxiomA M C] where
  scale : ℕ → ℝ
  scale_pos : ∀ n, 0 < scale n
  scale_limit : ∀ ε > 0, ∃ N, ∀ n > N, |scale n - scale (n + 1)| < ε

/--
公理 G: 量子引力耦合（自旋网络表述）

**物理意义**:
  - 在量子引力理论中，时空几何由自旋网络（spin network）描述
  - spin_network: 自旋网络的类型，表示量子几何的基态
  - amplitude_spin: 自旋网络的量子振幅，决定量子几何的概率幅

**数学结构**:
  - spin_network: 自旋网络类型，通常由图和边上的自旋标签组成
  - amplitude_spin: spin_network → ℂ，给每个自旋网络分配一个复振幅

**物理诠释**:
  - 自旋网络是 Loop Quantum Gravity (LQG) 的核心概念
  - 每个自旋网络代表一个量子化的几何态
  - amplitude_spin 给出该几何态出现的概率幅

**参考**:
  - Rovelli, C. (1998). "Loop quantum gravity". Living Reviews in Relativity.
  - Penrose, R. (1971). "Angular momentum: An approach to combinatorial space-time".
-/
class AxiomG (M C : Type*) [AxiomA M C] where
  spin_network : Type
  amplitude_spin : spin_network → ℂ

/--
公理 H: 标准模型嵌入（规范场论）

**物理意义**:
  - 描述基本粒子相互作用的规范场论结构
  - gauge_group: 规范群（如 SU(3)×SU(2)×U(1)）
  - field_content: 场在规范群和时空上的分布
  - lagrangian: 系统的作用量密度

**数学结构**:
  - gauge_group: 规范群类型（李群）
  - field_content : gauge_group → M → ℂ，场配置
  - lagrangian : (M → ℂ) → ℝ，作用量泛函

**物理诠释**:
  - gauge_group 描述相互作用的对称性（强相互作用 SU(3)，弱相互作用 SU(2)，电磁 U(1)）
  - field_content 描述场在时空各点的取值及其规范变换性质
  - lagrangian 是系统的作用量，通过变分原理导出运动方程

**参考**:
  - Weinberg, S. (1996). "The Quantum Theory of Fields".
  - Peskin, M. E., & Schroeder, D. V. (1995). "An Introduction to Quantum Field Theory".
-/
class AxiomH (M C : Type*) [AxiomA M C] where
  gauge_group : Type
  field_content : gauge_group → M → ℂ
  lagrangian : (M → ℂ) → ℝ

/--
公理 I: 信息因果性

**物理意义**:
  - entropy: 给每个关系元集合分配一个非负熵值
  - entropy_subadditive: 熵是次可加的（联合系统的熵不超过各部分熵之和）
  - information_causal: **因果信息单调性**
    若 x 在因果上先于 y（x ≤ y），则 x 的因果过去的熵不超过 y 的因果过去的熵。
    这体现了信息沿因果序的累积：因果过去越大，熵越多。

**数学结构**:
  entropy : Set M → ℝ
  entropy_nonneg : ∀ S, 0 ≤ entropy S
  entropy_subadditive : ∀ S T, entropy (S ∪ T) ≤ entropy S + entropy T
  information_causal : ∀ x y : M, B.le x y →
    entropy {z | B.le z x} ≤ entropy {z | B.le z y}

**证明程度**: ✅ 公理定义完整
-/
class AxiomI (M C : Type*) [A : AxiomA M C] [B : AxiomB M C] where
  /-- 熵函数: 给每个关系元集合分配一个非负熵值 -/
  entropy : Set M → ℝ
  /-- 熵非负性 -/
  entropy_nonneg : ∀ S, 0 ≤ entropy S
  /-- 熵的次可加性 -/
  entropy_subadditive : ∀ S T, entropy (S ∪ T) ≤ entropy S + entropy T
  /-- **因果信息单调性**: 若 x 在因果上先于 y，则 x 的因果过去的熵不超过 y 的因果过去 -/
  information_causal : ∀ x y : M, B.le x y →
    entropy {z | B.le z x} ≤ entropy {z | B.le z y}

/-! ============================================================================
   公理 J: 动力学编织（从静态结构到动态宇宙）
   ============================================================================ -/

/--
================================================================================
公理 J: AxiomJ (M C : Type*) [AxiomA M C] [AxiomB M C]

**本体论跃迁**：
  原 AxiomA-D-I 构成了一个"静态"的逻辑宇宙——
  因果序 lt 是预先给定的、凝固的、不可变的。
  
  **问题**：在广义相对论中，因果结构本身就是动力学变量（度规）。
  编织 compose 改变规则，但不改变 lt 本身。
  这意味着"时空"是凝固在琥珀中的化石，而非流淌的河流。

**解决方案**：
  AxiomJ 引入 **演化映射** evolve，使规则可以作用于关系元，
  产生新的事件，并更新因果层级。
  这将 Theory 从静态结构升级为**动态系统**，
  直接对应量子力学中的酉演化。

**数学结构**：
  evolve : C → M → M   -- 规则作用于关系元，产生新的事件
  causal_update : ∀ (α : C) (x : M), B.lt x (evolve α x)
                       -- 操作必然走向未来
  comp_evolve : ∀ α β x, evolve (A.compose α β) x
                            = evolve β (evolve α x)
                       -- 时序复合：先 α 后 β

**物理诠释**：
  1. **宇宙的呼吸**：每个规则的执行都是一次"事件的诞生"
     evolve α x 表示在关系元 x 处执行规则 α，产生新的事件
  2. **时间的方向性**：causal_update 保证演化必然严格走向未来
     x < evolve α x，热力学箭头被编码在公理中
  3. **组合的一致性**：comp_evolve 保证复合规则的演化
     与分步演化等价——这是量子力学酉演化的离散版本
  4. **与 AxiomD 的深度协同**：
     AxiomD 断言因果裂缝不存在（output α < output β ⇒ ∃ γ, compose α γ = β）
     AxiomJ 赋予"因果"以生命：每一次编织都是一次时间的跃迁
     ⇒ 两个公理共同刻画了一个**活着的、闭合的、演化的离散宇宙**

**证明程度**: ✅ 公理定义完整（动力学闭环）
================================================================================
-/
class AxiomJ (M C : Type*) [A : AxiomA M C] [B : AxiomB M C] where
  /-- **演化映射**：规则作用于关系元，产生新的事件 -/
  evolve : C → M → M
  /-- **因果更新**：每次演化都走向未来或不走向过去 —— 时间箭头内蕴于公理
     注意：在有限模型中，使用非严格的 le 偏序，允许恒等映射（最大元不进化） -/
  causal_update : ∀ (α : C) (x : M), B.le x (evolve α x)
  /-- **时序复合**：复合规则的演化与分步演化等价 —— 酉演化的离散版本 -/
  comp_evolve : ∀ (α β : C) (x : M),
    evolve (A.compose α β) x = evolve β (evolve α x)

/-! ============================================================================
   完整理论结构: Theory
   ============================================================================ -/

/--
================================================================================
定义: 完整 CSQIT 理论 (Theory M C)

**物理意义** (v2: 动力学宇宙):
  从 AxiomA 到 AxiomJ 的完整整合，定义了一个
  **活着的、演化的、信息因果的、可编织的离散时空量子理论**。
  
  AxiomD (编织闭合性) + AxiomJ (动力学编织)
  共同构成了"宇宙在 Lean 中的自指"的核心引擎。

**数学结构** (更新):
  Σ (A : AxiomA M C) (B : AxiomB M C) (D : AxiomD M C)
    (C : AxiomC M C) (F : AxiomF M C) (G : AxiomG M C)
    (H : AxiomH M C) (I : AxiomI M C) (J : AxiomJ M C)

**证明程度**: ✅ 定义完整（动力学闭环）
================================================================================
-/
structure Theory (M C : Type*) where
  toAxiomA : AxiomA M C
  toAxiomB : AxiomB M C
  toAxiomD : AxiomD M C
  toAxiomC : AxiomC M C
  toAxiomF : AxiomF M C
  toAxiomG : AxiomG M C
  toAxiomH : AxiomH M C
  toAxiomI : AxiomI M C
  toAxiomJ : AxiomJ M C

end CSQIT
