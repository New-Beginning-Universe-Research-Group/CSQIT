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
  roots := #[
    `Core.Axioms,
    `Core.Theorems,
    `Core.Models.FinModels,
    `Core.Models.EnhancedModels,
    `Core.HDST,
    `Core.Consistency,
    `Core.Independence,
    `Core.AxiomD_Independence,
    `Core.AxiomC_Independence,
    `Core.WeavingStructure,
    `Core.Hierarchy,
    `Core.Unified,
    `Core.Summary,
    `Core.Philosophy,
    `Core.OpenProblems,
    `Core.README
  ]
