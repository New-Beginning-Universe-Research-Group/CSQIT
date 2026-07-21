/-
CSQIT — 壳层容量 2n² 公式（元素周期律的代数本质）
文件: DerivedLaws/Chemistry/ShellCapacity.lean
版本: v11.6.0
日期: 2026-07-19
编译状态: ⏸ 未参与编译（未在 lakefile.lean 中注册）

================================================================================
定律名称：壳层容量公式 2n²（元素周期律的核心）
================================================================================

化学中的对应：
  元素周期表中，第 n 个电子壳层最多容纳 2n² 个电子。
  这是化学元素周期性排列的基础——
  2, 8, 18, 32, ... 这些数字决定了元素周期表的形状。

CSQIT 中的对应：
  第 n 层的状态数 = 2 * n²
  因子 n² 来自角动量的代数结构（前 n 个奇数之和 = n²）
  因子 2 来自两面性（每个状态有两个极性/自旋）

依赖层级：🟡 W2 框架性
  数学核心（前 n 个奇数和 = n²）：🔵 W1 严格（纯数学习题）
  物理对应链条：
    - "n² = 角动量态数"：🟡 W2 框架性（需要旋转对称假设）
    - "因子 2 = 两面性/自旋"：🟡 W2 框架性（需要两面性-自旋对应）
    - "2n² = 电子壳层容量"：🟠 W3 诠释

物理意义：
  元素周期表的 2n² 规律不是"上帝的设计"或"巧合"，
  而是两个更基本事实的结果：
  1. 角动量/旋转的代数结构给出 n² 个状态
  2. 两面性（自旋/手性/极性）给出因子 2

适用范围：
  - 适用于所有具有旋转对称性 + 两面性的系统
  - 在相对论性更强的区域，精细结构修正会出现，但 2n² 的主体结构不变
  - 这解释了为什么周期表是这个样子，而不是别的样子
================================================================================
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace CSQIT.DerivedLaws.Chemistry

open Finset

/--
核心数学恒等式：前 n 个奇数的和 = n²

  ∑_{k=0}^{n-1} (2k+1) = n²

几何意义：
  一个 n×n 的正方形可以分解为 n 个连续的 L 形层，
  第 k 层（从0开始数）有 2k+1 个格子。

物理意义：
  第 n 壳层的轨道数 = n²
  （不考虑自旋/两面性的情况下）
-/
theorem sum_of_odd_numbers (n : ℕ) :
    ∑ k ∈ range n, (2 * k + 1) = n ^ 2 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    ring_nf
    <;> omega

/--
壳层容量公式：第 n 壳层最多容纳 2 * n² 个状态

因子 2 的来源：两面性（每个轨道有两个态）
因子 n² 的来源：角动量代数结构（前 n 个奇数之和）

这就是元素周期表的"2n² 规律"的代数本质。
-/
theorem shell_capacity_formula (n : ℕ) :
    2 * (∑ k ∈ range n, (2 * k + 1)) = 2 * n ^ 2 := by
  rw [sum_of_odd_numbers n]

/--
稀有气体的原子序数序列：
  第 n 个稀有气体的原子序数 = 2 * ∑_{k=1}^n k²
                 = n(n+1)(2n+1)/3

验证：
  n=1: 2               → He (2)  ✔
  n=2: 2+8 = 10        → Ne (10) ✔
  n=3: 2+8+18 = 28     → ... （实际是18，但Ar是18，因为3d在4s之后填充）
  n=4: 2+8+18+32 = 60  → ...

注意：实际周期表中由于能级交错（n+l规则），顺序不完全是按壳层填充的。
但 2n² 作为每个壳层的最大容量是严格成立的。
-/
theorem noble_gas_cumulative_capacity (n : ℕ) :
    ∑ k ∈ range n, (2 * (k + 1) ^ 2) = n * (n + 1) * (2 * n + 1) / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    ring_nf
    <;> omega

/--
两面性因子定理：
  如果每个基本状态有两个变体（自旋向上/向下，或两面性的两个面），
  那么总状态数乘以 2。

这是 CSQIT 中"因子 2"的来源——
不是因为"电子有自旋"这个额外假设，
而是因为因果结构的两面性本质。
-/
theorem two_aspect_factor (n : ℕ) :
    2 * n = n + n := by
  ring

end CSQIT.DerivedLaws.Chemistry
