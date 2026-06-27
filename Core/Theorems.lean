/-
CSQIT 核心定理汇总
文件: Core/Theorems.lean

本文件是 CSQIT 核心定理的统一入口，导入并汇总各子模块的核心定理。

模块结构:
- Core.Axioms              — 公理系统定义
- Core.CausalWeaving       — 因果序与编织定理
- Core.AmplitudeTheorems   — 振幅结构定理
- Core.TwoAspectTheorems   — 一体两面性定理
- Core.Models.FinModels    — Fin 具体模型
- Core.Models.EnhancedModels — 增强模型
- Core.WeavingStructure    — 编织结构（增强公理系统）
- Core.HierarchicalWeaving — 层级编织理论
- Core.Hierarchy           — 层级结构
-/

import Core.Axioms
import Core.CausalWeaving
import Core.AmplitudeTheorems
import Core.TwoAspectTheorems

namespace CSQIT

set_option linter.unusedVariables false

/-! ============================================================================
   CSQIT 核心定理总览
   ============================================================================

   本文件汇总 CSQIT 理论的核心定理。所有定理已按主题拆分到各子模块中，
   可通过子命名空间直接访问。

   ## 1. 因果序与编织定理 (CausalWeaving)

   核心定理:
   - `CausalWeaving.input_must_be_empty` — 核心坍缩定理：所有规则输入恒为空
   - `CausalWeaving.causal_le_refl` — 因果偏序自反性
   - `CausalWeaving.causal_le_trans` — 因果偏序传递性
   - `CausalWeaving.causal_le_antisymm` — 因果偏序反对称性
   - `CausalWeaving.strict_order_irrefl` — 严格因果序非自反性
   - `CausalWeaving.strict_order_trans` — 严格因果序传递性
   - `CausalWeaving.weaving_implies_output_not_in_input` — 编织蕴含输出不在输入中

   ## 2. 振幅结构定理 (AmplitudeTheorems)

   核心定理:
   - `AmplitudeTheorems.compose_idempotent_amplitude` — 幂等规则振幅为 1
   - `AmplitudeTheorems.unit_rule_amplitude_one` — 单位元规则振幅为 1

   振幅基本性质（来自 AxiomC）:
   - `AxiomC.norm_one` — 振幅幺正性：|amplitude α|² = 1
   - `AxiomC.comp_rule` — 振幅同态性：amplitude(compose α β) = amplitude α * amplitude β
   - `AxiomC.amplitude_injective` — 振幅单射性

   ## 3. 一体两面性定理 (TwoAspectTheorems)

   核心定理:
   - `TwoAspectTheorems.left_transitive` — 左可迁性定义
   - `TwoAspectTheorems.output_degenerate_theorem` — 左可迁群中 output 退化
   - `TwoAspectTheorems.two_aspect_asymmetry_in_finite_group_models` — 两面性不对称定理
   - `TwoAspectTheorems.amplitude_inner_duality` — 振幅内在两面性（模+相位）
   - `TwoAspectTheorems.local_whole_has_two_aspects` — 局部整体的两面性
   - `TwoAspectTheorems.infinite_whole_simple_not_bounded` — 无限整体不可闭合
   - `TwoAspectTheorems.has_nontrivial_weaving` — 非空洞编织定义
   - `TwoAspectTheorems.left_transitive_no_weaving` — 左可迁群中无编织
   ============================================================================ -/

/-! ============================================================================
   哲学总结: CSQIT 的理论结构
   ============================================================================

   CSQIT 公理系统（AxiomA - AxiomJ）描述了一个离散时空信息本体论，
   其核心特征是"一体两面性"：

   1. **因果面 (Causal Aspect)**
      - 由 AxiomA 的 output 函数和 AxiomB 的因果序 ≤ 刻画
      - 描述规则在时空结构中的"位置"
      - 在群结构下倾向于退化（output 为常函数）

   2. **信息面 (Informational Aspect)**
      - 由 AxiomC 的 amplitude 函数刻画
      - 描述规则的量子信息内容
      - 在群结构下可以高度非平凡（单射）

   3. **两面性的不对称性**
      - 有限群模型中，因果面退化但信息面非平凡
      - 这不是设计选择，而是公理的数学必然结果
      - 物理对应: 量子力学中振幅非平凡而时空背景"固定"

   4. **编织的涌现性**
      - input_must_be_empty 表明编织不需要外部输入
      - 编织是内禀的代数和因果结构的涌现
      - 这是"空输入编织"的深刻数学含义

   5. **有限与无限的辩证**
      - 有限局部整体必有两面（内部+外部）
      - 无限整体可能是"单面"的（没有外部）
      - 这暗示了宇宙作为整体的独特本体论地位
   ============================================================================ -/

end CSQIT
