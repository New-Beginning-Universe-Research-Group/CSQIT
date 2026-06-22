import Lake
open Lake DSL

package csqit where
  version := v!"10.5.0"

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc6"

-- ⚠️ 诚实标注（2026-06-20，依据评审报告 P0-3 建议）：
-- `Appendices/` 目录下的 .lean 文件**不包含在此编译目标中**。
-- 这些文件包含与标准模型、引力、宇宙学等主题相关的"手写数学"，
-- 它们被刻意保留为"阅读材料"而非可编译代码，因为它们尚未被
-- 形式化证明。当它们被转换为可编译的 Lean 代码后，
-- 应将其加入 Core/ 目录，并在这里的 roots 中登记。

lean_lib CSQIT where
  -- ⚠️ roots 按依赖关系的拓扑顺序排列
  -- 阅读顺序：基础公理 → 定理 → 模型 → 分析/综合 → 文档
  roots := #[
    `Core.Axioms,              -- 1. 基础：公理体系定义（所有其他模块依赖此）
    `Core.Theorems,            -- 2. 核心定理（依赖 Axioms）
    `Core.Models.FinModels,     -- 3. 有限模型构造（依赖 Axioms, Theorems）
    `Core.Models.EnhancedModels,-- 4. 增强模型（依赖 Axioms, Theorems, FinModels）
    `Core.HDST,                -- 5. HDST 模型（依赖 Axioms）
    `Core.WeavingStructure,    -- 6. 编织结构分析（依赖 Axioms, Theorems）
    `Core.Hierarchy,           -- 7. 公理层次关系（依赖 Axioms, Theorems）
    `Core.Consistency,         -- 8. 一致性证明（依赖 Axioms, Theorems, FinModels）
    `Core.Independence,        -- 9. 独立性证明（依赖 Axioms, Theorems）
    `Core.AxiomD_Independence, -- 10. AxiomD 独立性（依赖 Axioms, Theorems）
    `Core.AxiomC_Independence, -- 11. AxiomC 独立性（依赖 Axioms, Theorems）
    `Core.Unified,             -- 12. 统一框架（依赖上述大部分模块）
    `Core.Summary,             -- 13. 项目总结（依赖上述模块）
    `Core.Philosophy,          -- 14. 物理哲学背景（文档性质）
    `Core.OpenProblems,        -- 15. 开放问题（依赖上述模块）
    `Core.README               -- 16. 模块说明（最后）
  ]
