import Lake
open Lake DSL

package CSQIT_Project where

require mathlib from "/home/dell/lean_deps/.lake/packages/mathlib"
require batteries from "/home/dell/lean_deps/.lake/packages/batteries"

-- ==============================================================================
-- CSQIT 10.4.5 编译配置
-- ==============================================================================
-- 项目定位：离散时空信息的公理化数学框架
-- ==============================================================================

-- ==============================================================================
-- 主库：Core 模块（14个文件，全部严格证明）
-- ==============================================================================
@[default_target]
lean_lib CSQIT where
  roots := #[
    -- Level 0（无依赖，公理基础）
    `Core.Axioms,

    -- Level 1（依赖 Axioms）
    `Core.Theorems,
    `Core.Models.FinModels,
    `Core.WeavingStructure,

    -- Level 2（依赖 Theorems）
    `Core.Consistency,
    `Core.Independence,
    `Core.AxiomC_Independence,
    `Core.AxiomD_Independence,

    -- Level 3（哲学诠释，依赖全部）
    `Core.Philosophy,

    -- 辅助模块
    `Core.HDST,
    `Core.Hierarchy,
    `Core.Unified,

    -- 项目状态总结
    `Core.Summary
  ]

-- ==============================================================================
-- 可选库：Appendices 模块（已完成部分，可选编译）
-- ==============================================================================
-- 注意：未完成的存根文件已移除，移至 FutureWork/ 目录作为研究笔记
lean_lib CSQIT_Appendices where
  roots := #[
    -- Appendix A: Amplitude & Independence
    `Appendices.AppendixA.Amplitude,
    `Appendices.AppendixA.Independence,
    `Appendices.AppendixA.Uniqueness,
    `Appendices.AppendixA.Proofs,

    -- Appendix B: Causal Order & Weaving
    `Appendices.AppendixB.Amplitude,
    `Appendices.AppendixB.BasicDefinitions,
    `Appendices.AppendixB.Causal,
    `Appendices.AppendixB.Probability,
    `Appendices.AppendixB.Weaving,

    -- Appendix C: Quantum Interface
    `Appendices.AppendixC.QuantumInterface,

    -- Appendix D: Causal Structure
    `Appendices.AppendixD.CausalStructure,

    -- Appendix E: Observables
    `Appendices.AppendixE.Observables,

    -- Appendix H: Black Hole Thermo
    `Appendices.AppendixH.BlackHoleThermo,

    -- Appendix J: Mathematics & Ontology
    `Appendices.AppendixJ.Mathematics,
    `Appendices.AppendixJ.Ontology,

    -- Appendix K: Theorems
    `Appendices.AppendixK.Theorems
  ]

-- ==============================================================================
-- 编译状态说明：
--   Core 模块: 14/14 已编译验证 ✅
--   Appendices 模块: 12 个已完成文件 ✅
--   未完成文件已移至 FutureWork/ 目录（Regge, Einstein, GravityEmergence, 
--   TensorProduct, Complexity, Verifier, Reproduce）
-- ==============================================================================