/-
CSQIT 10.4.5 HDST 层级结构
文件: Core/Hierarchy.lean
版本: 10.4.5 (Canonical Textbook Edition)
日期: 2026-06-15

================================================================================
概述
================================================================================

本文件定义 HDST（Hierarchical Discrete Spacetime Theory）层级结构：
1. **HierarchyParameters** - 层级参数结构（基础层级、层级增量）
2. **hierarchyScaleTable** - 层级尺度表（线性尺度函数）
3. **重要层级索引** - 普朗克尺度、可观察宇宙等特殊层级

================================================================================
验证状态
================================================================================

✅ 类型定义：完整
✅ 层级参数：完整（含正性约束）
✅ 层级尺度表：完整
✅ 定理：非负性、单调性、对称性
✅ 编译通过
✅ 无 sorry / 无 admit

================================================================================
-/

import Core.Axioms
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic

namespace CSQIT.Hierarchy

open CSQIT

/-! ============================================================================
   第一部分：层级参数定义
   ============================================================================ -/

/-- **层级参数结构**

**物理意义**:
  定义 HDST 层级结构的基本参数。
  - baseLevel : ℕ - 基础层级索引（普朗克尺度层级）
  - delta     : ℕ - 层级增量（层级间尺度差异）
  - h_delta_pos : 0 < delta - 增量为正的约束

**数学结构**:
  参数都是自然数，约束编码为证明项。
-/
structure HierarchyParameters where
  baseLevel : ℕ     -- 基础层级索引
  delta     : ℕ     -- 层级增量
  h_delta_pos : 0 < delta   -- 增量为正（约束）

/-! ----------------------------------------------------------------------------
   层级参数的基本定理
   ---------------------------------------------------------------------------- -/

/-- 层级增量正性：0 < params.delta -/
theorem HierarchyParameters.delta_pos (params : HierarchyParameters) :
    0 < params.delta := params.h_delta_pos

/-- 层级增量非零：params.delta ≠ 0 -/
theorem HierarchyParameters.delta_ne_zero (params : HierarchyParameters) :
    params.delta ≠ 0 := Nat.ne_of_gt params.h_delta_pos

/-- 层级增量至少为 1：params.delta ≥ 1 -/
theorem HierarchyParameters.delta_ge_one (params : HierarchyParameters) :
    params.delta ≥ 1 := Nat.one_le_iff_ne_zero.mpr params.delta_ne_zero

/-! ============================================================================
   第二部分：层级尺度表
   ============================================================================ -/

/-- **层级尺度表**

**物理意义**:
  给每个整数层级赋予一个尺度值。
  层级越大，尺度越大（对应更宏观的物理尺度）。

**数学定义**:
  hierarchyScaleTable params n := params.baseLevel + n.natAbs * params.delta

**关键性质**:
  1. 非负性：所有层级尺度都是非负自然数
  2. 单调性：|n| ≤ |m| → scaleTable(n) ≤ scaleTable(m)
  3. 对称性：scaleTable(n) = scaleTable(-n)
-/
def hierarchyScaleTable (params : HierarchyParameters) : ℤ → ℕ :=
  fun n => params.baseLevel + (n.natAbs) * params.delta

/-- **层级尺度非负性定理**

所有层级尺度都是非负的（即 ≥ 0）。-/
theorem hierarchyScaleTable_nonneg (params : HierarchyParameters) (n : ℤ) :
    0 ≤ hierarchyScaleTable params n := by
  simp only [hierarchyScaleTable]
  exact Nat.zero_le _

/-- **层级尺度单调性定理**

如果 |n| ≤ |m|，则 scaleTable(n) ≤ scaleTable(m)。-/
theorem hierarchyScaleTable_mono (params : HierarchyParameters) (n m : ℤ)
    (h : n.natAbs ≤ m.natAbs) :
    hierarchyScaleTable params n ≤ hierarchyScaleTable params m := by
  simp only [hierarchyScaleTable]
  have h' : n.natAbs * params.delta ≤ m.natAbs * params.delta :=
    Nat.mul_le_mul_right params.delta h
  exact Nat.add_le_add_left h' params.baseLevel

/-- **层级零对应基础层级**

层级索引为零时，尺度等于基础层级（普朗克尺度）。-/
@[simp]
theorem hierarchyScaleTable_zero (params : HierarchyParameters) :
    hierarchyScaleTable params 0 = params.baseLevel := by
  simp [hierarchyScaleTable]

/-- **层级正一对应基础层级加增量**

层级索引为 1 时，尺度 = baseLevel + delta。-/
@[simp]
theorem hierarchyScaleTable_one (params : HierarchyParameters) :
    hierarchyScaleTable params 1 = params.baseLevel + params.delta := by
  simp [hierarchyScaleTable]

/-- **层级负一与正一有相同尺度（对称性）**

scaleTable(-1) = baseLevel + delta = scaleTable(1)。-/
@[simp]
theorem hierarchyScaleTable_neg_one (params : HierarchyParameters) :
    hierarchyScaleTable params (-1) = params.baseLevel + params.delta := by
  simp [hierarchyScaleTable]

/-- **尺度表的一般对称性定理**

scaleTable(n) = scaleTable(-n)。
正负层级有相同的尺度。-/
theorem hierarchyScaleTable_symmetric (params : HierarchyParameters) (n : ℤ) :
    hierarchyScaleTable params n = hierarchyScaleTable params (-n) := by
  simp only [hierarchyScaleTable]
  rw [Int.natAbs_neg]

/-! ============================================================================
   第三部分：特殊层级定义
   ============================================================================ -/

/-- **可观察宇宙层级索引**

物理意义：从普朗克尺度（10^-35 m）到可观察宇宙（10^27 m）
约有 log10(10^27 / 10^-35) = log10(10^62) ≈ 62 个数量级。
取近似值 60。
-/
def observableUniverseIndex : ℤ := 60

/-- 可观察宇宙层级索引为正（60 > 0） -/
theorem observableUniverseIndex_pos : 0 < observableUniverseIndex := by
  simp only [observableUniverseIndex]
  norm_num

/-- 可观察宇宙的尺度 = baseLevel + 60 * delta -/
theorem observableUniverse_scale (params : HierarchyParameters) :
    hierarchyScaleTable params observableUniverseIndex =
      params.baseLevel + 60 * params.delta := by
  simp [hierarchyScaleTable, observableUniverseIndex]

/-- **普朗克尺度层级**

物理意义：最小物理尺度层级，
  对应层级 0。
-/
def planckScale (params : HierarchyParameters) : ℕ := params.baseLevel

/-- 普朗克尺度 = 基础层级。 -/
@[simp]
theorem planckScale_eq_baseLevel (params : HierarchyParameters) :
    planckScale params = params.baseLevel := rfl

/-- 普朗克尺度 = 层级 0 的尺度。 -/
theorem planckScale_eq_zero_level (params : HierarchyParameters) :
    planckScale params = hierarchyScaleTable params 0 := by
  simp [planckScale, hierarchyScaleTable]

/-- **普朗克尺度是最小尺度**

普朗克尺度 ≤ 任何其他层级的尺度。
这对应量子引力的最小尺度假设。-/
theorem planckScale_minimal (params : HierarchyParameters) (n : ℤ) :
    planckScale params ≤ hierarchyScaleTable params n := by
  simp only [planckScale, hierarchyScaleTable]
  exact Nat.le_add_right params.baseLevel (n.natAbs * params.delta)

end CSQIT.Hierarchy