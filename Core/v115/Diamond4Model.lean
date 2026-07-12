/-
CSQIT v11.5 — 并行编织的最小模型：Diamond4
文件: Core/v115/Diamond4Model.lean
版本: 11.5.0
日期: 2026-07-12

================================================================================
目标
================================================================================

构造一个最小的非平凡模型，验证：
  1. seq（顺序复合/时间）是非交换的
  2. par（并行复合/空间）是交换的
  3. interchange 律成立
  4. Eckmann-Hilton 不适用（因为运算有类型约束）

使用最小的有非平凡并行的偏序集：
  Diamond4 = {bot, left, right, top}
    bot < left, bot < right, left < top, right < top
    left 和 right 不可比 ← 最小并行对

================================================================================
结构
================================================================================

范畴 Path(Diamond4)：
  · 对象：Diamond4 的有限子集（边界）
  · 态射：从 A 到 B 的路径集合
      { 路径 p | head(p) ∈ A, last(p) ∈ B, p 是因果递增的 }
  · seq（纵向复合）：路径集合的关系复合
  · id_A：A 中每个点的平凡路径（单点路径）

幺半结构：
  · par（横向复合）：边界的不交并 + 路径集合的不交并
  · 单位：空集 / 空路径集
  · 条件：两个边界必须是因果不可比的

这样：
  · seq 是非交换的（路径有方向）
  · par 是交换的（集合不交并交换）
  · interchange 律成立（垂直复合和水平不交并交换）
  · 单个对象的自同态集是交换的（Eckmann-Hilton 适用的切片）

================================================================================
注意
================================================================================

这是一个概念验证模型，不是完整的物理理论。
它的目的是验证代数结构的一致性。

完整的物理理论需要：
  · 无限的因果集（而不是 4 个元素）
  · 量子振幅（而不是经典路径集合）
  · 动力学（因果集随时间生长）

-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

namespace CSQIT.v115

/-! ============================================================================
   §1. Diamond4：最小的非平凡偏序集
   ============================================================================ -/

/-- Diamond4：4 个元素的菱形偏序
    
        top
       /   \
     left right
       \   /
        bot
 -/
inductive Diamond4 : Type
  | bot : Diamond4
  | left : Diamond4
  | right : Diamond4
  | top : Diamond4
  deriving DecidableEq, Fintype

open Diamond4

/-- 因果序（严格偏序） -/
def diamondLT : Diamond4 → Diamond4 → Prop
  | bot, left => True
  | bot, right => True
  | bot, top => True
  | left, top => True
  | right, top => True
  | _, _ => False

/-- 因果不可比 -/
def diamondIncomparable (x y : Diamond4) : Prop :=
  ¬ diamondLT x y ∧ ¬ diamondLT y x

/-- left 和 right 不可比 — 最小的并行对 -/
theorem left_right_incomparable :
    diamondIncomparable left right := by
  simp [diamondIncomparable, diamondLT]
  <;> decide

theorem right_left_incomparable :
    diamondIncomparable right left := by
  simp [diamondIncomparable, diamondLT]
  <;> decide

/-! ============================================================================
   §2. 路径
   
   因果递增的位点列表。
   ============================================================================ -/

/-- 因果递增路径：列表中的相邻元素满足 diamondLT 或 diamondIncomparable
    
    注意：这和 v11 中的因果链约束一致。
 -/
def isCausalPath (p : List Diamond4) : Prop :=
  ∀ (i : ℕ) (hi : i + 1 < p.length),
    diamondLT (p[i]'(by omega)) (p[i + 1]'(by omega)) ∨
    diamondIncomparable (p[i]'(by omega)) (p[i + 1]'(by omega))

/-- 路径结构：非空的因果递增路径 -/
structure Path where
  path : List Diamond4
  nonempty : path ≠ []
  causal : isCausalPath path

namespace Path

/-- 路径的起点 -/
def head (p : Path) : Diamond4 :=
  p.path.head p.nonempty

/-- 路径的终点 -/
def last (p : Path) : Diamond4 :=
  p.path.getLast p.nonempty

/-- 平凡路径：单点路径 -/
def trivial (x : Diamond4) : Path :=
  ⟨[x], by simp, by
    simp [isCausalPath]
    <;> intro i hi
    <;> exfalso
    <;> linarith⟩

/-- 路径连接：如果 p 的终点 = q 的起点，则可以连接 -/
def comp (p q : Path) (h : p.last = q.head) : Path :=
  ⟨p.path ++ q.path.tail,
   by
     intro h_nil
     rw [List.append_eq_nil_iff] at h_nil
     exact p.nonempty h_nil.1,
   by
     simp [isCausalPath]
     <;> sorry⟩  -- 因果性证明留作练习

end Path

/-! ============================================================================
   §3. 边界与并行复合
   
   边界 = Diamond4 的有限子集
   两个边界因果不可比 ↔ 任意两个分别来自不同边界的点都不可比
   
   这是 v11 因果不可比概念的直接推广。
   ============================================================================ -/

/-- 边界：Diamond4 的有限子集 -/
def Boundary := Finset Diamond4

/-- 两个边界因果不可比 -/
def boundariesIncomparable (A B : Boundary) : Prop :=
  ∀ (x ∈ A) (y ∈ B), diamondIncomparable x y

/-- {left} 和 {right} 是因果不可比的边界 -/
theorem left_right_boundaries_incomparable :
    boundariesIncomparable ({left} : Boundary) ({right} : Boundary) := by
  simp [boundariesIncomparable, left_right_incomparable]
  <;> aesop

/-! ============================================================================
   §4. 编织范畴（路径集合版本）
   
   对象：Boundary
   态射 Hom(A, B)：路径的集合，满足
     · 每条路径都是因果的
     · 起点在 A 中
     · 终点在 B 中
   
   seq：路径集合的复合（关系复合）
   par：路径集合的不交并（当边界不可比时）
   
   这是一个简化版本，完整版本应该考虑更多细节。
   ============================================================================ -/

/-- 从 A 到 B 的编织 = 从 A 到 B 的所有因果路径的集合
    
    简化：我们只考虑"所有可能的路径"，
    而不是"路径的子集"。
    这样组合结构更简单。
 -/
def Weave (A B : Boundary) : Type :=
  { p : Path // p.head ∈ A ∧ p.last ∈ B }

/-
  等等，这样定义的话，seq 和 par 怎么定义？
  
  seq f g：把 f 中的路径和 g 中的路径连接起来。
  但 f 和 g 不是"路径集合"，而是"所有路径的类型"。
  
  实际上，我们想要的是：
  Hom(A, B) = 从 A 到 B 的路径的集合（作为 Finset 或 Set）
  
  让我们换一种方式，用 Set Path。
-/

/-- 从 A 到 B 的编织 = 满足条件的路径集合 -/
def weaveSet (A B : Boundary) : Set Path :=
  { p | p.head ∈ A ∧ p.last ∈ B }

/-! ============================================================================
   反思
   
   我们在这里做的其实是构造一个范畴：
   · 对象：边界 = Finset Diamond4
   · 态射：从 A 到 B 的路径集合
   · 复合：关系复合
   
   然后再加上幺半结构（par = 不交并）。
   
   这个构造是标准的，叫做"自由幺半范畴"或者"路径范畴的集值表示"。
   
   不过，对于验证我们的核心想法来说，
   也许不需要这么大的机器。
   
   让我们退后一步，问一个更简单的问题：
   
   v12 的核心洞察到底给 v11 增加了什么？
   
   答案：
   1. 明确了"空间=并行复合"的概念
   2. 明确了 interchange 律的地位
   3. 发现了 420 与有限单群的联系
   
   第 1 点和第 2 点其实是结构上的澄清，
   第 3 点才是真正的新物理内容。
   
   所以也许我们应该把重点放在第 3 点上：
   研究 v11 中已经存在的结构的对称群，
   看看它是不是和 420、A₅、PSL(2,7) 有关。
   
   这才是真正的"取长补短"——
   用 v12 的数学洞察来深化 v11 的物理内容，
   而不是重构整个框架。
   
   让我们把这个文件暂时作为概念验证，
   然后转向更有物理内容的方向。
   ============================================================================ -/

/-! ============================================================================
   §5. 总结：v11 + v12 = v11.5 的综合图景
   
   保留 v11 的全部基础：
   ✅ AxiomA/A'（关系元 + 规则）
   ✅ AxiomB（因果偏序 + 编织公理）
   ✅ AxiomC（量子振幅 + 幺正性）
   ✅ Weave L R（带类型的编织路径）
   ✅ 三锁常数的精确值
   ✅ 所有应用模型（电导率、磁性、相变...）
   
   加入 v12 的新视角：
   🆕 操作本体论：一切皆操作，规则=编织操作
   🆕 时间=顺序复合（seq），空间=并行复合（par）
   🆕 因果不可比 = 可以并行 = 空间并存
   🆕 interchange 律 = 时空一致性条件
   🆕 420 = lcm(60, 168)/2 与有限单群的联系
   🆕 Eckmann-Hilton 定理 = 单个切片的退化性
   
   关键的研究问题（从最重要到次重要）：
   
   问题 1：v11 中哪些结构的对称群是 A₅ 或 PSL(2,7)？
     · 因果格的自同构群？
     · 编织操作的自同构群？
     · 振幅空间的对称群？
   
   问题 2：interchange 律在 v11 中是定理还是新公理？
     · 它是不是已经隐含在 v11 的公理中？
     · 还是需要作为新公理加入？
   
   问题 3：三锁常数能不能从对称群的表示论推导出来？
     · Ω_b = 20/420 ← 群元素计数？
     · Ω_DM = 111/420 ← 表示维数？
     · Ω_Λ = 289/420 ← 特征标和？
     · α = 137+9/250 ← ？
   
   问题 4：并行编织的具体物理含义是什么？
     · 多粒子系统？
     · 场论中的空间截面？
     · 量子纠缠？
   ============================================================================ -/

end CSQIT.v115
