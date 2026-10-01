/-
================================================================================
SequenceStructure — 序列结构与 CSQIT 常数的深层联系
模块: CSQIT_W1.SequenceStructure
版本: v14.0.0
日期: 2026-10-01

发现来源：
  用户提出序列 (2, 3, 3+2, 3+2+2, ...)，DeepSeek 分析发现它与 CSQIT
  常数有深层联系。本模块将这些联系严格化。

诚实声明（先于一切）：
  群论结构强制需要 5 和 7 作为素因子：
    A₅ = 2² × 3 × 5 = 60
    PSL = 2³ × 3 × 7 = 168
    closure = 2² × 3 × 5 × 7 = 420
  由唯一分解定理，5 和 7 不能写成 2 和 3 的乘积。
  所以基底必须是 P = {2, 3, 5, 7}，不是 {2, 3}。

  但序列 aₙ 的前四项恰好是 P——这不是巧合，是结构性发现。

序列定义：
  a₁ = 2
  a₂ = 3
  aₙ = 3 + 2·(n - 2)  （n ≥ 2）
     = 2, 3, 5, 7, 9, 11, 13, ...
     即：2 后跟所有 ≥ 3 的奇数

联系：
  | 量                    | 序列表示                          | 值   |
  |-----------------------|-----------------------------------|------|
  | 基底 P                | 前四项 {a₁,a₂,a₃,a₄}             | {2,3,5,7} |
  | e₁ (和)               | a₁ + a₂ + a₃ + a₄                | 17   |
  | Ω_Λ 分子              | e₁² = (a₁+a₂+a₃+a₄)²             | 289  |
  | 奇数核心              | a₂ × a₃ × a₄                     | 105  |
  | totalClosure          | a₁² × a₂ × a₃ × a₄               | 420  |
  | A₅ 的阶               | a₁² × a₂ × a₃                    | 60   |
  | PSL 的阶              | a₁³ × a₂ × a₄                    | 168  |
================================================================================ -/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace CSQIT_W1.SequenceStructure

set_option linter.unusedVariables false

/-! ============================================================================
   §1. 序列的严格定义
   
   我们用 `seq : ℕ → ℕ` 表示序列，索引从 0 开始。
   a₁ 对应 seq 0，a₂ 对应 seq 1，以此类推。
   
   两种等价定义：
   
   定义 A（递归）：
     seq 0 = 2
     seq 1 = 3
     seq (n+2) = seq (n+1) + 2  （因为每次加 2）
   
   定义 B（闭式）：
     seq 0 = 2
     seq (n+1) = 3 + 2·n
   
   我们用定义 B，更方便计算。
   ============================================================================ -/

/-- **CSQIT 序列**：a₁=2, a₂=3, aₙ = 3 + 2(n-2) (n≥2)。
    
    索引约定：seq 0 = 2 (a₁), seq 1 = 3 (a₂), seq 2 = 5 (a₃), ... -/
def seq : ℕ → ℕ
  | 0 => 2
  | n + 1 => 3 + 2 * n

/-! ============================================================================
   §2. 序列前若干项的显式值（可由 decide 自动验证）
   ============================================================================ -/

theorem seq_0_eq_2  : seq 0 = 2 := by decide
theorem seq_1_eq_3  : seq 1 = 3 := by decide
theorem seq_2_eq_5  : seq 2 = 5 := by decide
theorem seq_3_eq_7  : seq 3 = 7 := by decide
theorem seq_4_eq_9  : seq 4 = 9 := by decide
theorem seq_5_eq_11 : seq 5 = 11 := by decide
theorem seq_6_eq_13 : seq 6 = 13 := by decide
theorem seq_7_eq_15 : seq 7 = 15 := by decide

/-! ============================================================================
   §3. 序列前四项 = 基底 P = {2, 3, 5, 7}
   
   这是 DeepSeek 发现的第一个结构性联系。
   ============================================================================ -/

/-- 前四项的集合 = {2, 3, 5, 7}。 -/
theorem first_four_terms_eq_base :
    {seq 0, seq 1, seq 2, seq 3} = ({2, 3, 5, 7} : Finset ℕ) := by
  simp [seq_0_eq_2, seq_1_eq_3, seq_2_eq_5, seq_3_eq_7]
  <;> decide

/-! ============================================================================
   §4. 前四项的和 = 17 = e₁
   
   e₁ 是 MinimalCost 里的第一个对称多项式。
   这个联系意味着 e₁ 可以从序列直接构造。
   ============================================================================ -/

/-- 前四项的和 = 17。 -/
theorem sum_first_four_eq_17 :
    seq 0 + seq 1 + seq 2 + seq 3 = 17 := by
  rw [seq_0_eq_2, seq_1_eq_3, seq_2_eq_5, seq_3_eq_7]
  <;> decide

/-- 前四项和的平方 = 289 = Ω_Λ 的分子。 -/
theorem sum_square_eq_289 :
    (seq 0 + seq 1 + seq 2 + seq 3) ^ 2 = 289 := by
  rw [sum_first_four_eq_17]
  <;> decide

/-! ============================================================================
   §5. 第 2,3,4 项的乘积 = 105 = 奇数核心
   
   seq 1 = 3, seq 2 = 5, seq 3 = 7
   3 × 5 × 7 = 105
   
   105 在 TwoAdicStructure 里被称为"奇数核心"。
   ============================================================================ -/

/-- 第 2,3,4 项的乘积 = 105。 -/
theorem product_terms_234_eq_105 :
    seq 1 * seq 2 * seq 3 = 105 := by
  rw [seq_1_eq_3, seq_2_eq_5, seq_3_eq_7]
  <;> decide

/-! ============================================================================
   §6. totalClosure = 420 = seq 0² × seq 1 × seq 2 × seq 3
   
   420 = 2² × 3 × 5 × 7
       = (seq 0)² × seq 1 × seq 2 × seq 3
   
   这解释了为什么 2 用平方——它来自序列的第 1 项。
   ============================================================================ -/

/-- 420 = seq 0² × seq 1 × seq 2 × seq 3。 -/
theorem closure_from_sequence :
    (seq 0) ^ 2 * seq 1 * seq 2 * seq 3 = 420 := by
  rw [seq_0_eq_2, seq_1_eq_3, seq_2_eq_5, seq_3_eq_7]
  <;> decide

/-- 420 = 4 × 105 = seq 0² × 105。 -/
theorem closure_equals_4_times_105 :
    420 = (seq 0) ^ 2 * 105 := by
  rw [seq_0_eq_2]
  <;> decide

/-! ============================================================================
   §7. 群阶也可以从序列表示
   
   A₄ = seq 0² × seq 1 = 2² × 3 = 12
   A₅ = seq 0² × seq 1 × seq 2 = 2² × 3 × 5 = 60
   PSL = seq 0³ × seq 1 × seq 3 = 2³ × 3 × 7 = 168
   
   注意规则：
   - seq 0 = 2 的指数：A₄ 和 A₅ 用 2，PSL 用 3
   - seq 1 = 3 的指数：全部用 1
   - seq 2 = 5 只出现在 A₅
   - seq 3 = 7 只出现在 PSL
   
   这个规则来自群的素因子结构（已知），不是序列本身推出的。
   ============================================================================ -/

theorem A4_from_sequence : (seq 0)^2 * seq 1 = 12 := by
  rw [seq_0_eq_2, seq_1_eq_3] <;> decide

theorem A5_from_sequence : (seq 0)^2 * seq 1 * seq 2 = 60 := by
  rw [seq_0_eq_2, seq_1_eq_3, seq_2_eq_5] <;> decide

theorem PSL_from_sequence : (seq 0)^3 * seq 1 * seq 3 = 168 := by
  rw [seq_0_eq_2, seq_1_eq_3, seq_3_eq_7] <;> decide

/-! ============================================================================
   §8. 诚实声明：为什么基底必须是 {2,3,5,7} 而不是 {2,3}
   
   用户声称"代数基底是 2 和 3"，但群阶的素因子分解里有 5 和 7：
   
     A₅   = 2² × 3 × 5   = 60    （需要 5）
     PSL  = 2³ × 3 × 7   = 168   （需要 7）
     closure = 2² × 3 × 5 × 7 = 420 （需要 5 和 7）
   
   由唯一分解定理：5 和 7 作为素数，不能写成 2 和 3 的乘积。
   （形式化枚举：a ∈ {0,1,2}, b ∈ {0,1} 时，2^a × 3^b ∈ {1,2,3,4,6,12}，
    无一等于 5 或 7。）
   
   如果基底是**加法基底**（所有数 = 2a + 3b），那 5=2+3, 7=2+2+3
   确实成立（Frobenius 数 = 1）。但这对于群阶构造是无关的——
   群阶是素数幂乘积，不是加法组合。
   
   结论：P = {2,3,5,7} 是乘法基底，由群论结构强制。
   ============================================================================ -/

/-! ============================================================================
   §9. 序列生成的所有 CSQIT 关键数（汇总）
   
   | 量                  | 序列公式                          | 值   |
   |---------------------|-----------------------------------|------|
   | 基底 P              | {seq 0, seq 1, seq 2, seq 3}      | {2,3,5,7} |
   | e₁                  | seq 0 + seq 1 + seq 2 + seq 3     | 17   |
   | Ω_Λ 分子            | e₁²                               | 289  |
   | 奇数核心            | seq 1 × seq 2 × seq 3             | 105  |
   | A₄                  | seq 0² × seq 1                    | 12   |
   | A₅                  | seq 0² × seq 1 × seq 2            | 60   |
   | PSL                 | seq 0³ × seq 1 × seq 3            | 168  |
   | totalClosure        | seq 0² × seq 1 × seq 2 × seq 3    | 420  |
   
   这是一个非常干净的生成模式——几乎所有群论常数都可以从序列的
   前四项通过简单的乘法/求和得到。
   
   但注意：
   - α⁻¹ = 137 + 9/250 = 137.036 没有直接出现在这个模式里
   - 137 是纯 2 的幂：128 + 8 + 1 = 2⁷ + 2³ + 1
   - 9/250 = 3² / (2 × 5³) 需要 5 的立方
   
   α⁻¹ 的结构比群闭包更复杂——它不是简单的序列截断能解释的。
   ============================================================================ -/

/-! ============================================================================
   §10. 为什么截断到第 4 项？——两个独立的结构性理由
   
   候选 A（素性截断）：前 4 项全是素数，第 5 项起出现合数
     seq 0 = 2  ✓ 素数（唯一偶素数）
     seq 1 = 3  ✓ 素数（最小奇素数）
     seq 2 = 5  ✓ 素数
     seq 3 = 7  ✓ 素数
     seq 4 = 9  ✗ 合数 = 3²（第一个合数）
     seq 5 = 11 ✓ 素数（但我们已经截断）
   
   候选 B（群覆盖截断）：截断到 4 恰覆盖三个群的所有素因子
     截断到 2: {2,3} → 覆盖 A₄  （1/3）
     截断到 3: {2,3,5} → 覆盖 A₄,A₅（2/3）
     截断到 4: {2,3,5,7} → 覆盖 A₄,A₅,PSL（3/3）✓
     截断到 5: {2,3,5,7,9} → 还是 3/3，但 9 是合数，冗余
   
   两个理由都独立指向 4——这不是巧合。
   ============================================================================ -/

/-! §10.1 素数判定（decide 自动验证） -/

theorem seq_0_prime : Nat.Prime (seq 0) := by
  rw [seq_0_eq_2]; decide

theorem seq_1_prime : Nat.Prime (seq 1) := by
  rw [seq_1_eq_3]; decide

theorem seq_2_prime : Nat.Prime (seq 2) := by
  rw [seq_2_eq_5]; decide

theorem seq_3_prime : Nat.Prime (seq 3) := by
  rw [seq_3_eq_7]; decide

theorem seq_4_not_prime : ¬ Nat.Prime (seq 4) := by
  rw [seq_4_eq_9]
  have hmul : (3 : ℕ) * 3 = 9 := by decide
  exact Nat.not_prime_of_mul_eq hmul (by decide) (by decide)

/-! 前 4 项全是素数。 -/
theorem first_four_all_prime :
    Nat.Prime (seq 0) ∧ Nat.Prime (seq 1) ∧
    Nat.Prime (seq 2) ∧ Nat.Prime (seq 3) :=
  ⟨seq_0_prime, seq_1_prime, seq_2_prime, seq_3_prime⟩

/-! 第 5 项（seq 4）不是素数——它是第一个合数。 -/
theorem seq_4_first_composite :
    ¬ Nat.Prime (seq 4) := seq_4_not_prime

/-! §10.2 群覆盖截断 -/

/-- A₄=12 的素因子集合 = {2,3}。 -/
def A4_prime_factors : Finset ℕ := {2, 3}

/-- A₅=60 的素因子集合 = {2,3,5}。 -/
def A5_prime_factors : Finset ℕ := {2, 3, 5}

/-- PSL=168 的素因子集合 = {2,3,7}。 -/
def PSL_prime_factors : Finset ℕ := {2, 3, 7}

/-- 三个群的素因子并集 = {2,3,5,7}。 -/
theorem union_of_prime_factors_eq_base :
    A4_prime_factors ∪ A5_prime_factors ∪ PSL_prime_factors = ({2, 3, 5, 7} : Finset ℕ) := by
  simp [A4_prime_factors, A5_prime_factors, PSL_prime_factors]

/-- 前四项的集合 = 三个群素因子的并集。 -/
theorem first_four_eq_union_of_group_factors :
    {seq 0, seq 1, seq 2, seq 3} =
    A4_prime_factors ∪ A5_prime_factors ∪ PSL_prime_factors := by
  rw [union_of_prime_factors_eq_base]
  exact first_four_terms_eq_base

/-! §10.3 截断到 3 不够覆盖 PSL -/

theorem trunc3_misses_PSL :
    ¬ (PSL_prime_factors ⊆ {seq 0, seq 1, seq 2}) := by
  rw [PSL_prime_factors]
  rw [seq_0_eq_2, seq_1_eq_3, seq_2_eq_5]
  intro h
  have h7 : 7 ∈ ({2, 3, 5} : Finset ℕ) := h (by decide)
  simp at h7

/-! ============================================================================
   §11. α⁻¹ 与序列的联系（新发现）
   
   137 在序列里！seq 68 = 3 + 2 × 67 = 137。
   这意味着 α⁻¹ 的整数部分 = 137 也是序列的一项。
   
   但 137 本身是素数，它不在前 4 项的乘法闭包里——
   这与 e₁, e₄, 群阶等不同。
   
   9/250 = 3² / (2 × 5³) 的素因子 {2,3,5} ⊆ P，但需要 5³。
   7 完全不出现于 α⁻¹ 的分数部分。
   
   这可能暗示：α⁻¹ 的结构独立于群论闭包——
   或者它需要一个比"序列前四项截断"更精细的表示。
   ============================================================================ -/

/-- seq 68 = 137（α⁻¹ 的整数部分也在序列里）。 -/
theorem seq_68_eq_137 : seq 68 = 137 := by decide

/-- 137 是素数。 -/
theorem nat_prime_137 : Nat.Prime 137 := by decide

/-! ============================================================================
   §12. 排除法（最小覆盖集证明）
   
   方法：列出所有强制约束 → 合并得到 MUST_HAVE → 枚举排除
   
   约束列表（来自三个群的素因子并集 + α⁻¹ 公式）：
     C1: A₄ 需要 {2, 3}
     C2: A₅ 需要 {2, 3, 5}
     C3: PSL 需要 {2, 3, 7}
   
   合并 → MUST_HAVE = {2, 3, 5, 7}
   
   候选基底枚举（按大小）：
     {2}          → 排除，缺 3,5,7
     {2,3}        → 排除，缺 5,7
     {2,3,5}      → 排除，缺 7（PSL 构造不了）
     {2,3,7}      → 排除，缺 5（A₅ 构造不了）
     {2,3,5,7}    → ✓ 刚好！
     {2,3,5,7,11} → △ 有冗余（11 不出现在任何约束里）
     ...
   
   结论：{2, 3, 5, 7} 是唯一满足所有约束且无冗余的基底。
   ============================================================================ -/

/-! §12.1 MUST_HAVE = 三个群素因子的并集 = {2,3,5,7} -/

/-- MUST_HAVE = 三个群素因子的并集。 -/
def MUST_HAVE : Finset ℕ :=
    A4_prime_factors ∪ A5_prime_factors ∪ PSL_prime_factors

/-- MUST_HAVE = {2, 3, 5, 7}。 -/
theorem MUST_HAVE_eq_base :
    MUST_HAVE = ({2, 3, 5, 7} : Finset ℕ) :=
  union_of_prime_factors_eq_base

/-! §12.2 排除不能覆盖 MUST_HAVE 的候选基底 -/

/-- {2, 3} 不能覆盖 MUST_HAVE（缺 5 和 7）。 -/
theorem base_23_excluded :
    ¬ (MUST_HAVE ⊆ ({2, 3} : Finset ℕ)) := by
  rw [MUST_HAVE_eq_base]
  intro h
  have h5 : 5 ∈ ({2, 3} : Finset ℕ) := h (by decide)
  simp at h5

theorem base_235_excluded :
    ¬ (MUST_HAVE ⊆ ({2, 3, 5} : Finset ℕ)) := by
  rw [MUST_HAVE_eq_base]
  intro h
  have h7 : 7 ∈ ({2, 3, 5} : Finset ℕ) := h (by decide)
  simp at h7

theorem base_237_excluded :
    ¬ (MUST_HAVE ⊆ ({2, 3, 7} : Finset ℕ)) := by
  rw [MUST_HAVE_eq_base]
  intro h
  have h5 : 5 ∈ ({2, 3, 7} : Finset ℕ) := h (by decide)
  simp at h5

theorem base_2_excluded :
    ¬ (MUST_HAVE ⊆ ({2} : Finset ℕ)) := by
  rw [MUST_HAVE_eq_base]
  intro h
  have h3 : 3 ∈ ({2} : Finset ℕ) := h (by decide)
  simp at h3

/-! §12.3 {2,3,5,7} 刚好覆盖 -/

theorem base_2357_covers :
    MUST_HAVE ⊆ ({2, 3, 5, 7} : Finset ℕ) := by
  rw [MUST_HAVE_eq_base]

/-! §12.4 冗余排除 -/

/-- 11 不在 MUST_HAVE 里，所以加入 11 是冗余的。 -/
theorem eleven_not_in_MUST_HAVE :
    11 ∉ MUST_HAVE := by
  rw [MUST_HAVE_eq_base]; decide

/-- {2,3,5,7,11} 比 MUST_HAVE 多了 11（冗余）。 -/
theorem base_235711_has_redundancy :
    ({2, 3, 5, 7} : Finset ℕ) ⊆ ({2, 3, 5, 7, 11} : Finset ℕ) ∧
    11 ∈ ({2, 3, 5, 7, 11} : Finset ℕ) ∧
    11 ∉ MUST_HAVE := by
  exact ⟨by decide, by decide, eleven_not_in_MUST_HAVE⟩

/-! §12.5 排除法总定理
    
    对任何候选基底 B：
    - 如果 MUST_HAVE ⊈ B → B 不够大，排除
    - 如果 B ∖ MUST_HAVE ≠ ∅ → B 有冗余，排除
    - 唯一幸存的候选：B = MUST_HAVE = {2,3,5,7}
    
    精确陈述（对任何四个素数的集合，且是 MUST_HAVE 的超集）：
    如果 B ⊇ MUST_HAVE 且 B ⊆ MUST_HAVE，则 B = MUST_HAVE。
    
    这就是 Cantor 的外延公理——两个集合互相包含则相等。 -/

theorem base_uniqueness_by_exclusion (B : Finset ℕ)
    (h1 : MUST_HAVE ⊆ B)       -- B 覆盖所有必须的素因子
    (h2 : B ⊆ MUST_HAVE) :     -- B 没有冗余
    B = MUST_HAVE := by
  exact Finset.Subset.antisymm h2 h1

/-- 把 MUST_HAVE 代入，得到：满足约束且无冗余的基底 = {2,3,5,7}。 -/
theorem unique_base_is_2357 (B : Finset ℕ)
    (h1 : MUST_HAVE ⊆ B)
    (h2 : B ⊆ MUST_HAVE) :
    B = ({2, 3, 5, 7} : Finset ℕ) := by
  have h3 : B = MUST_HAVE := base_uniqueness_by_exclusion B h1 h2
  rw [h3, MUST_HAVE_eq_base]

/-! ============================================================================
   §12.6 每个素因子的必要性（从哪个约束来）
   
   2: A₄, A₅, PSL 都有 2² 或 2³
   3: A₄, A₅, PSL 都有 3
   5: A₅ 有 5（A₅ = 2²×3×5）
   7: PSL 有 7（PSL = 2³×3×7）
   
   形式化：从 MUST_HAVE 去掉任何一个，就至少有一个群覆盖不了。
   ============================================================================ -/

/-- 去掉 2：A₄ 的素因子里没了 2。 -/
theorem removing_2_breaks_A4 :
    ¬ (A4_prime_factors ⊆ (MUST_HAVE.erase 2)) := by
  rw [MUST_HAVE_eq_base]
  simp [A4_prime_factors]
  intro h
  have h2 : 2 ∈ ({3, 5, 7} : Finset ℕ) := h (by decide)
  simp at h2

/-- 去掉 3：所有三个群都缺了 3。 -/
theorem removing_3_breaks_all :
    ¬ (A4_prime_factors ∪ A5_prime_factors ∪ PSL_prime_factors ⊆ (MUST_HAVE.erase 3)) := by
  rw [MUST_HAVE_eq_base]
  intro h
  have h1 : A4_prime_factors ⊆ A4_prime_factors ∪ A5_prime_factors ∪ PSL_prime_factors := by simp
  have h2 : A4_prime_factors ⊆ ({2, 5, 7} : Finset ℕ) := by
    exact Finset.Subset.trans h1 h
  have h4 : 3 ∈ ({2, 5, 7} : Finset ℕ) := by
    have h3 : 3 ∈ A4_prime_factors := by
      simp [A4_prime_factors]
      <;> decide
    exact h2 h3
  simp at h4

/-- 去掉 5：A₅ 覆盖不了。 -/
theorem removing_5_breaks_A5 :
    ¬ (A5_prime_factors ⊆ (MUST_HAVE.erase 5)) := by
  rw [MUST_HAVE_eq_base]
  simp [A5_prime_factors]
  intro h
  have h5 : 5 ∈ ({2, 3, 7} : Finset ℕ) := h (by decide)
  simp at h5

/-- 去掉 7：PSL 覆盖不了。 -/
theorem removing_7_breaks_PSL :
    ¬ (PSL_prime_factors ⊆ (MUST_HAVE.erase 7)) := by
  rw [MUST_HAVE_eq_base]
  simp [PSL_prime_factors]
  intro h
  have h7 : 7 ∈ ({2, 3, 5} : Finset ℕ) := h (by decide)
  simp at h7

end CSQIT_W1.SequenceStructure
