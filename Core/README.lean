/-
CSQIT Core 模块依赖图（严格证明层级）

===========================================
===         CSQIT 10.4.5 架构         ===
===========================================

Level 0（无依赖，公理基础）:
  └── Core/Axioms.lean        ← 定义 AxiomA-J（10个公理类）
      ├── AxiomA: 关系元和规则的基本结构
      ├── AxiomB: 因果序（偏序关系）
      ├── AxiomC: 振幅（复值振幅函数）
      ├── AxiomD: 操作编织（le-而非 lt-）
      ├── AxiomF: 连续极限（⚠️ 实例退化，scale _ := 1）
      ├── AxiomG: 量子引力耦合（⚠️ 实例退化，amplitude_spin _ := 1）
      ├── AxiomH: 标准模型嵌入（⚠️ 实例退化，lagrangian _ := 0）
      ├── AxiomI: 信息因果性与熵（✅ 非平凡实例）
      └── AxiomJ: 动力学编织（新修订，le-而非 lt-）

Level 1（依赖Axioms）:
  ├── Core/Theorems.lean      ← 推导基本定理（8个核心定理）
  │     ├── input_must_be_empty (核心坍缩定理)
  │     ├── causal_intrinsicality (因果传递性)
  │     ├── amplitude_unit (振幅幺正性)
  │     └── weaving_closure (编织闭合性)
  │
  ├── Core/Models/FinModels.lean ← 构造非平凡有限模型
  │     ├── trivialModel
  │     ├── boolModel
  │     └── nonTrivialFinModel
  │
  └── Core/WeavingStructure.lean ← 编织结构定义（涌现性质）
        └── 从独立公理到涌现性质的重新诠释

Level 2（依赖Theorems）:
  ├── Core/Consistency.lean   ← 一致性证明
  │     └── 证明公理体系的内部一致性
  │
  └── Core/Independence.lean  ← 独立性证明
        └── 证明AxiomA-D的独立独立性

Level 3（哲学诠释，依赖全部）:
  └── Core/Philosophy.lean    ← DSIO 形式化（离散时空信息本体论）
        ├── 关系自足性
        ├── 因果内蕴性
        ├── 信息守恒
        ├── 时空涌现
        └── 编织闭合性

附加模块（辅助）:
  ├── Core/HDST.lean          ← HDST（高阶离散时空）整合
  ├── Core/Hierarchy.lean     ← 层级结构
  ├── Core/Unified.lean       ← 统一结构
  ├── Core/AxiomC_Independence.lean ← AxiomC独立性证明
  └── Core/Summary.lean       ← 项目总结与状态报告

===========================================
===         编译依赖顺序               ===
===========================================

1. Core/Axioms.lean
2. Core/Theorems.lean
3. Core/Models/FinModels.lean
4. Core/WeavingStructure.lean
5. Core/Consistency.lean
6. Core/Independence.lean
7. Core/Philosophy.lean
8. Core/HDST.lean
9. Core/Hierarchy.lean
10. Core/Unified.lean
11. Core/AxiomC_Independence.lean
12. Core/Summary.lean

===========================================
===         公理依赖关系               ===
===========================================

AxiomB ─→ AxiomA
AxiomC ─→ AxiomA
AxiomD ─→ AxiomA, AxiomB
AxiomE ─→ AxiomA, AxiomC
AxiomF ─→ AxiomA, AxiomB
AxiomG ─→ AxiomA, AxiomC
AxiomH ─→ AxiomA, AxiomB
AxiomI ─→ AxiomA, AxiomB, AxiomH

===========================================
===         定理依赖关系               ===
===========================================

input_must_be_empty         ← AxiomA
causal_intrinsicality       ← AxiomA, AxiomB
amplitude_unit              ← AxiomC
weaving_closure             ← AxiomD
emergence_theorem           ← WeavingStructure
dsio_theorems               ← 全部公理

===========================================
===         项目状态（诚实版）         ===
===========================================

Core模块:      14 个 Lean 文件 + Models/FinModels.lean = 14 个文件 + 1 个子目录
证明完整性:    无 `sorry`（OpenProblems.lean 中的标注为有意标记）
数学严谨性:    ✅ 所有定理有 Lean 4 形式化证明
公理一致性:    ✅ 通过非平凡有限模型（Fin 5, Fin 4）构造证明
物理相关性:    ⚠️ 仅在有限类型、退化实例上验证（AxiomF/G/H 均为常数）
可复现性:      ⚠️ lakefile 已定义，编译成功依赖正确配置的 mathlib（需 lake update）

⚠️ HDST 模型:   命名有误导性。M=Unit, C=Unit，数学上等价于 trivialModel。
               详见 Core/HDST.lean 顶部的诚实免责声明。

===========================================
===         引用格式                   ===
===========================================

当引用本项目时，请使用:
  CSQIT 10.4.5: Axiomatic Foundation for Discrete Spacetime
  Information Ontology, 2026

-/

namespace CSQIT.Core

end CSQIT.Core