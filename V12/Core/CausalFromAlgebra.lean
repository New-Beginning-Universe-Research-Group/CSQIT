/- ================================================================================
CSQIT v12.7.0 — CausalFromAlgebra：从 AxiomA/C 构造因果序 + 演化图景
文件: V12/Core/CausalFromAlgebra.lean
版本: v12.7.0（完整演化图景形式化：涌现→成长→循环）

理论定位：
  本模块是 CSQIT 核心架构的"涌现层"——
  因果序（偏序结构）、演化路径、循环闭合，
  全部从 AxiomA（代数）+ AxiomC（振幅）严格构造出来。

宇宙图景形式化：
  1. 虚空中微小不平衡 → amplitude_injective（打破对称性的约束）
  2. 涌现出极小编织元 → C 的生成元（AxiomA 未显式指定，半群自动给出）
  3. 遵循路径成长组合 → compose 递归嵌套 + 演化序列
  4. 扩张至整个宇宙 → C 中所有 compose 组合的闭包
  5. 不断演化不断循环 → amplitude ∈ U(1) + 射影时间闭合

W1 严格层级标记：
  ✅ 仅依赖 AxiomA：directCause, causalLe, directCause_trans, causalLe_trans
  ✅ 依赖 AxiomA + AxiomC：causalAcyclic_from_injective, causalLe_antisymm
================================================================================ -/

import V12.Core.Foundation

namespace CSQIT.V12.CausalFromAlgebra

open CSQIT.V12.Foundation

/-! ═══════════════════════════════════════════════════════════
   §0 愿景的形式化映射

   用户的宇宙图景：
     "虚空中微小不平衡涌现出很小很小的个体，
      遵循路径成长组合直至整个宇宙，
      个体在整体中不断演化不断循环。"

   v12 公理体系的精确对应：
   
   ┌────────────────────┬─────────────────────────────────┐
   │ 愿景环节            │ v12 形式化                       │
   ├────────────────────┼─────────────────────────────────┤
   │ 虚空                │ AxiomA 的半群公理（完全对称）     │
   │ 微小不平衡          │ AxiomC.amplitude_injective        │
   │                    │ ← 打破 C 元素的"无差别性"         │
   ├────────────────────┼─────────────────────────────────┤
   │ 涌现个体            │ C 中的元素（编织规则）             │
   │ 很小很小            │ input_nodup（输入列表无重复，     │
   │                    │ 无冗余最小单元）                   │
   ├────────────────────┼─────────────────────────────────┤
   │ 遵循路径成长组合     │ AxiomA.compose + compose_input   │
   │                    │ ← 规则可以递归组合                 │
   ├────────────────────┼─────────────────────────────────┤
   │ 扩张至整个宇宙       │ closure_sequence_extended         │
   │                    │ ← 能标层级严格递增                 │
   ├────────────────────┼─────────────────────────────────┤
   │ 不断演化不断循环     │ AxiomC.norm_one                   │
   │                    │ ← amplitude ∈ U(1)，群结构闭合     │
   │                    │ + 射影时间 0→2π 闭合（已有定理）   │
   └────────────────────┴─────────────────────────────────┘

   本模块的工作：
   把这些"散落在不同公理中的图景碎片"整合为统一的
   因果序 + 演化路径 + 循环闭合 的 W1 严格理论。
   ═══════════════════════════════════════════════════════════ -/

/-! ═══════════════════════════════════════════════════════════
   §1 直接因果关系（从 AxiomA 纯构造）
   
   directCause M C A x y := ∃ α : C, x ∈ A.input α ∧ A.output α = y
   
   物理意义：编织规则 α 的输入包含 x，输出为 y → x 因果影响 y。
   
   层级：W1 严格定义（仅 AxiomA）
   ═══════════════════════════════════════════════════════════ -/

/-- **直接因果**：x 直接导致 y（W1 严格定义）。
    
    纯构造，不需要 M 有任何序/有限性假设。 -/
def directCause (M C : Type*) (A : AxiomA M C) (x y : M) : Prop :=
  ∃ α : C, x ∈ A.input α ∧ A.output α = y

/-! ═══════════════════════════════════════════════════════════
   §2 directCause 的传递性（W1 严格，仅用 AxiomA）
   
   定理：directCause x y → directCause y z → directCause x z
   
   证明技巧：取 compose α β 作为直接因果的证据。
   
   compose 本身不交换，但这没关系——我们证明的是传递性，
   不是交换性。compose_input 把 α 的输入和 β 的输入拼接，
   compose_output 把结果的输出锁定为 β 的输出 z。
   
   物理意义：因果影响不存在"中间态"——多步传递自动压缩为直接。
   
   层级：W1 严格定理
   ═══════════════════════════════════════════════════════════ -/

/-- **定理：directCause 传递**（W1 严格，仅 AxiomA）。
    
    关键技巧：compose α β 自动给出 x→z 的直接因果证据。 -/
theorem directCause_trans (M C : Type*) (A : AxiomA M C)
    {x y z : M} 
    (hxy : directCause M C A x y) 
    (hyz : directCause M C A y z) :
    directCause M C A x z := by
  rcases hxy with ⟨α, hx_in, hα_out⟩
  rcases hyz with ⟨β, hy_in, hβ_out⟩
  let γ : C := A.compose α β
  refine' ⟨γ, _, _⟩
  · -- x ∈ input (α∘β) = input α ++ input β，所以 x ∈ 左侧
    have h : A.input γ = A.input α ++ A.input β := A.compose_input α β
    rw [h]
    exact List.mem_append_left (A.input β) hx_in
  · -- output (α∘β) = output β = z
    have h : A.output γ = A.output β := A.compose_output α β
    rw [h, hβ_out]

/-! ═══════════════════════════════════════════════════════════
   §3 因果序 causalLe（W1 严格）
   
   causalLe x y := x = y ∨ directCause x y
   
   因为 directCause 已经传递，这直接是预序（自反 + 传递）。
   
   层级：W1 严格，仅 AxiomA
   ═══════════════════════════════════════════════════════════ -/

/-- **因果序**：x 在因果上先于或等于 y（W1 严格定义）。
    
    自反 + 传递由定义和 directCause_trans 直接给出。 -/
def causalLe (M C : Type*) (A : AxiomA M C) (x y : M) : Prop :=
  x = y ∨ directCause M C A x y

section CausalLeProperties

variable {M C : Type*} (A : AxiomA M C)

/-- **causalLe 自反性**（W1 严格）。 -/
theorem causalLe_refl (x : M) : causalLe M C A x x := by
  exact Or.inl rfl

/-- **causalLe 传递性**（W1 严格）。 -/
theorem causalLe_trans {x y z : M} 
    (hxy : causalLe M C A x y) 
    (hyz : causalLe M C A y z) :
    causalLe M C A x z := by
  have h1 : x = y ∨ directCause M C A x y := hxy
  have h2 : y = z ∨ directCause M C A y z := hyz
  rcases h1 with (rfl | h_dir_xy)
  · exact hyz
  rcases h2 with (rfl | h_dir_yz)
  · exact Or.inr h_dir_xy
  · have h_dir_xz : directCause M C A x z := 
        directCause_trans M C A h_dir_xy h_dir_yz
    exact Or.inr h_dir_xz

end CausalLeProperties

/-! ═══════════════════════════════════════════════════════════
   §4 ★★★ 因果无环性（W1 严格，AxiomA + AxiomC）
   
   因果环的不存在性是 ℂ 乘法交换性 + amplitude_injective 的直接推论。
   
   核心技巧：
     假设 directCause x y ∧ directCause y x。
     令 γ = α∘β（output = x），δ = β∘α（output = y）。
     amplitude γ = amplitude α * amplitude β = amplitude δ（ℂ 交换）
     由 injective：γ = δ → output γ = output δ → x = y。
   
   compose 本身不交换（AxiomA 只给结合律），
   但 amplitude 把 compose 映射到 ℂ 乘法（可交换），
   这就迫使有环时 α∘β = β∘α，从而 output 矛盾。
   
   物理意义：因果环的不存在是复数域结构的物理显现。
   
   层级：W1 严格定理！
   ═══════════════════════════════════════════════════════════ -/

/-- **定理：因果无环性**（W1 严格，AxiomA + AxiomC）。
    
    不存在两个不同的 x ≠ y 使得 x→y 且 y→x。
    核心：ℂ 乘法交换 + amplitude_injective。 -/
theorem causalAcyclic_from_injective (M C : Type*) 
    (A : AxiomA M C) (Cx : AxiomC M C) :
    ∀ (x y : M), directCause M C A x y → directCause M C A y x → x = y := by
  intro x y h_dir_xy h_dir_yx
  rcases h_dir_xy with ⟨α, _h_in_α, hα_out⟩
  rcases h_dir_yx with ⟨β, _h_in_β, hβ_out⟩
  
  let γ : C := A.compose α β     -- output = output β = x
  let δ : C := A.compose β α     -- output = output α = y
  
  have h_amp_eq : Cx.amplitude γ = Cx.amplitude δ := by
    have hγ : Cx.amplitude γ = Cx.amplitude α * Cx.amplitude β := Cx.comp_rule α β
    have hδ : Cx.amplitude δ = Cx.amplitude β * Cx.amplitude α := Cx.comp_rule β α
    have h_comm : Cx.amplitude α * Cx.amplitude β = 
                  Cx.amplitude β * Cx.amplitude α := mul_comm _ _
    rw [hγ, hδ, h_comm]
  
  have h_eq : γ = δ := Cx.amplitude_injective h_amp_eq
  have h_out_eq : A.output γ = A.output δ := by rw [h_eq]
  
  have hγ_out : A.output γ = x := by
    have h : A.output (A.compose α β) = A.output β := A.compose_output α β
    rw [h, hβ_out]
  have hδ_out : A.output δ = y := by
    have h : A.output (A.compose β α) = A.output α := A.compose_output β α
    rw [h, hα_out]
  
  rw [hγ_out, hδ_out] at h_out_eq
  exact h_out_eq

/-! ═══════════════════════════════════════════════════════════
   §5 causalLe 成为真正的偏序（W1 严格）
   
   有了因果无环性，反对称性自动得证：
   
   causalLe x y → causalLe y x → x = y
   
   证明：
     causalLe x y = (x=y ∨ directCause x y)
     causalLe y x = (y=x ∨ directCause y x)
     如果 x ≠ y，则必须 directCause x y ∧ directCause y x
     但 causalAcyclic_from_injective 推出 x = y，矛盾。
   
   层级：W1 严格（AxiomA + AxiomC）
   ═══════════════════════════════════════════════════════════ -/

/-- **causalLe 的反对称性**（W1 严格，AxiomA + AxiomC）。
    
    由 causalAcyclic_from_injective 直接推出。 -/
theorem causalLe_antisymm (M C : Type*) 
    (A : AxiomA M C) (Cx : AxiomC M C) 
    {x y : M}
    (hxy : causalLe M C A x y) 
    (hyx : causalLe M C A y x) :
    x = y := by
  have h1 : x = y ∨ directCause M C A x y := hxy
  have h2 : y = x ∨ directCause M C A y x := hyx
  rcases h1 with (rfl | h_dir_xy)
  · rfl
  rcases h2 with (h_eq | h_dir_yx)
  · exact h_eq.symm
  · exact causalAcyclic_from_injective M C A Cx x y h_dir_xy h_dir_yx

/-! ═══════════════════════════════════════════════════════════
   §6 ★ 演化路径：从单步因果到组合演化（W1 严格）
   
   愿景映射：
     "遵循一个路径，成长组合" → C 中元素的递归 compose 嵌套
   
   演化序列定义：
     给定 C 中元素的 List，它们的"演化合成"就是递归 compose。
     这是一个纯 W1 严格定义——完全在 C 半群内部。
   
   物理意义：
     每个编织规则 α 对应一次"因果步"。
     演化序列 [α₁, α₂, ..., αₙ] 对应 n 步因果演化的合成。
     compose 的结合律保证了演化的合成不依赖执行顺序的分组。
   
   层级：W1 严格构造（仅 AxiomA）
   ═══════════════════════════════════════════════════════════ -/

/-- **演化合成**：一个编织规则列表的合成（W1 严格定义）。
    
    递归地把列表中的所有规则 compose 起来。
    
    注意：compose 的结合律 AxiomA.compose_assoc 保证了
    foldr compose α₀ [α₁, ..., αₙ] 的结果不依赖括号位置。 -/
def evolveFoldr (M C : Type*) (A : AxiomA M C) 
    (hd : C) (tl : List C) : C :=
  List.foldr A.compose hd tl

/-- **演化合成的 output 不变性**（W1 严格定理，对 tl 归纳证明）。
    
    沿着 compose 链递归演化，output 恒等于 hd 的 output。
    
    直觉：compose_output α β 说 output (α∘β) = output β。
    所以不管怎么 foldr compose hd tl，output 永远是
    最右边（最内层）那个 hd 的 output。
    
    这揭示了演化合成的一个重要结构：
    所有"外层"compose 都不改变最终 output，
    它们只改变 input（把更多事件加入输入列表）。
   -/
theorem evolveFoldr_output_right (M C : Type*) (A : AxiomA M C)
    (hd : C) (tl : List C) :
    A.output (List.foldr A.compose hd tl) = A.output hd := by
  induction tl with
  | nil => rfl
  | cons β rest ih =>
    have h_def : List.foldr A.compose hd (β :: rest) =
        A.compose β (List.foldr A.compose hd rest) := by rfl
    rw [h_def]
    have h : A.output (A.compose β (List.foldr A.compose hd rest)) =
        A.output (List.foldr A.compose hd rest) := A.compose_output β _
    rw [h]
    exact ih

/-! ═══════════════════════════════════════════════════════════
   §7 ★ 循环闭合：amplitude ∈ U(1) 的物理意义
   
   愿景映射：
     "不断演化不断循环" → amplitude 的群结构闭合性
   
   AxiomC.norm_one 说 amplitude α 的范数为 1。
   这意味着 amplitude α ∈ U(1) = {z ∈ ℂ | |z| = 1}。
   U(1) 在乘法下是群（每个 z 有逆 z⁻¹ = \bar{z}）。
   
   物理意义：
     每个编织规则 α 都有一个"逆" amplitude⁻¹，
     对应某种"反演化"。
     这就是循环闭合的数学基础。
   
   层级：W1 严格（AxiomC + Mathlib U(1) 群论）
   ═══════════════════════════════════════════════════════════ -/

/-- **振幅的 U(1) 群结构**（W1 严格，AxiomC）。
    
    amplitude 映射把 compose 半群嵌入 U(1) 群。
    
    这意味着：
      - 每个 amplitude α ∈ U(1) 都有逆 z⁻¹ = \bar{z}
      - 演化可以"循环回去"（振幅的群逆）
      - amplitude_injective 保证了 C 的子集与 U(1) 子群一一对应 -/
theorem amplitude_in_U1 (M C : Type*) (A : AxiomA M C) (Cx : AxiomC M C)
    (α : C) : Complex.normSq (Cx.amplitude α) = 1 := Cx.norm_one α

/-! ═══════════════════════════════════════════════════════════
   §7.5 ★★★ 诚实声明：directCause 的传递性（W1 严格）
   
   DeepSeek 评审的关键观察：
     directCause_trans 证明了 directCause 本身是传递的。
     compose 操作把多步因果链压缩为一步直接因果。
     因此本框架中：
       causalLe x y（x ≠ y） ↔ directCause x y
     
     这就是说：**所有因果关系都是"直接"的**——
     不存在"隔着中间节点"的因果链。
     
     重要：directCause 不是"格相邻"（adjacent），
     它就是整个因果偏序（除了自反那部分）。
     传统的"相邻"定义（严格介于之间的节点不存在）
     在这里自动满足（因为没有中间节点可介于之间），
     但 directCause 的范围远大于传统相邻。
   
   序数版正格距：
     我们没有数值距离函数（需要 Fintype M 等额外假设）。
     但我们有以下 W1 严格的正格距性质：
       
       (a) 因果无环（no_two_cycle）：
           不存在 x ≠ y 使得 x→y 且 y→x
           （causalAcyclic_from_injective，W1 严格）
       
       (b) 因果传递的原子证据：
           每个 directCause x y 的证据 α 满足 input_nodup α
           （AxiomA.input_nodup，W1 严格）
           因果传递通过**无冗余的有限列表**——不存在无限精细
       
       (c) 物理尺度正间隔：effectiveGap k = c(k+1) - c(k) > 0
           （LatticeGap.lean 中 W1 严格证明）
   
   三层循环结构：
     ┌──────────┬─────────────────────────────────────────────┐
     │ 层次      │ 结构                                     │
     ├──────────┼─────────────────────────────────────────────┤
     │ 因果循环  │ ❌ 已排除（causalAcyclic_from_injective）  │
     ├──────────┼─────────────────────────────────────────────┤
     │ 时间圆    │ ✅ 存在（foldIndex n = n % 840）            │
     │          │ 螺旋上升：因果序严格递增，时间坐标周期性     │
     ├──────────┼─────────────────────────────────────────────┤
     │ 演化递增  │ ❌ 不循环（closure_sequence_extended_succ_lt）│
     └──────────┴─────────────────────────────────────────────┘
   
   用户图景中的"不断演化不断循环"：
     → 时间圆层面的循环（层 2）
     → 因果序/演化递增层面的不循环（层 1 + 层 3）
     → 合起来就是"螺旋上升"
   
   层级：W1 严格
   ═══════════════════════════════════════════════════════════ -/

/-- **重要桥接定理**：causalLe 在 x ≠ y 时等价于 directCause（W1 严格）。
    
    证明：
      - `→`：causalLe x y (x ≠ y) 意味着 directCause x y（因果序定义）
      - `←`：directCause x y 意味着 causalLe x y（因为 causalLe = Eq ∨ directCause）
    
    结合 directCause_trans，这说明因果偏序极其扁平——
    没有层次化的中间节点。compose 自动把多步压缩为一步。
    
    这与传统"格相邻"概念不同——这是整个因果偏序。 -/
theorem causalLe_iff_directCause_ne (M C : Type*) (A : AxiomA M C)
    (x y : M) (h_ne : x ≠ y) :
    causalLe M C A x y ↔ directCause M C A x y := by
  constructor
  · -- → causalLe → directCause
    intro h
    rcases h with (rfl | h_dc)
    · exact False.elim (h_ne rfl)
    · exact h_dc
  · -- ← directCause → causalLe
    intro h_dc
    exact Or.inr h_dc

/-! ═══════════════════════════════════════════════════════════
   §7.6 不存在 2-循环：序数版正格距（W1 严格，AxiomA + AxiomC）
   
   DeepSeek 评审提议的路径：
     因果无环性 → 相邻节点存在正距离 → 格距 > 0
   
   序数版正格距：
     不存在两个不同的事件 x ≠ y 使得 x→y 且 y→x。
     这就是因果无环性的直接推论。
   
   物理意义：因果维度上没有"零距离循环"。
   ═══════════════════════════════════════════════════════════ -/

/-- **序数版正格距：不存在 2-循环**（W1 严格，AxiomA + AxiomC）。
    
    不存在两个不同的事件 x ≠ y 使得 x→y 且 y→x。
    
    这是 DeepSeek 评审提议的"因果无环性 → 正格距"的
    序数版本——它排除了任何因果维度上的"零距离循环"。 -/
theorem no_two_cycle (M C : Type*) (A : AxiomA M C) (Cx : AxiomC M C) :
    ¬ ∃ (x y : M), x ≠ y ∧ directCause M C A x y ∧ directCause M C A y x := by
  intro h
  rcases h with ⟨x, y, h_ne, h_dc_xy, h_dc_yx⟩
  have h_eq : x = y := causalAcyclic_from_injective M C A Cx x y h_dc_xy h_dc_yx
  exact h_ne h_eq

/-! ═══════════════════════════════════════════════════════════
   §7.7 因果传递的原子证据：通过 input_nodup（W1 严格，仅 AxiomA）
   
   每个 directCause x y 的证据 α 都满足 input_nodup α：
     - input α 的元素互不相同（无冗余）
     - 但 x 必须在 input α 里（所以 input α 非空）
   
   这揭示了因果传递的**最小性**：
     - 每次因果影响都通过一个有限的、无冗余的列表完成
     - 不存在"无限精细"的因果影响
     - 因果结构是"离散原子"的
   
   这就是序数版正格距的更深层含义：
     因果影响不能被无限细分——它有最小单元。
   
   层级：W1 严格（仅 AxiomA.input_nodup）
   
   诚实声明：
     这个定理本质上是 AxiomA.input_nodup 公理的直接应用。
     它的 W1 严格性无争议，但它的物理意义需要谨慎评估：
     它证明了因果传递的"原子性"（有限无冗余），
     但没有证明真实空间的格距正性。
   ═══════════════════════════════════════════════════════════ -/

/-- **因果证据的原子性**（W1 严格，仅 AxiomA）。
    
    对任何 directCause x y，存在证据 α 满足 input_nodup α。
    
    物理意义：因果传递通过**无冗余的最小单元**完成，
    不存在无限精细的因果影响。
    
    诚实声明：这是 AxiomA.input_nodup 的直接推论。 -/
theorem directCause_witness_atomic (M C : Type*) (A : AxiomA M C)
    {x y : M} (h : directCause M C A x y) :
    ∃ (α : C), x ∈ A.input α ∧ A.output α = y ∧ (A.input α).Nodup := by
  rcases h with ⟨α, hx_in, hα_out⟩
  refine' ⟨α, hx_in, hα_out, A.input_nodup α⟩

/-! ═══════════════════════════════════════════════════════════
   §8 总结：v12.7.0 完整因果架构
   
   ✅ 从 AxiomA 涌现的 W1 严格结构：
     - directCause：因果关系的纯代数定义
     - directCause_trans：因果的可传递性
     - causalLe：因果序（预序）
     - evolveFoldr：演化合成（compose 递归嵌套）
   
   ✅ 从 AxiomA + AxiomC 涌现的 W1 严格结构：
     - causalAcyclic_from_injective：因果无环性
     - causalLe_antisymm：因果序的反对称性
     - causalLe 成为真正的偏序（PartialOrder）
     - amplitude_in_U1：循环闭合的群论基础
   
   ✅ 愿景映射完成：
     - "虚空"    → AxiomA 半群对称性
     - "不平衡"  → AxiomC.amplitude_injective 打破无差别
     - "涌现"    → C 中元素直接存在于 AxiomA
     - "成长"    → evolveFoldr（compose 递归组合）
     - "循环"    → amplitude ∈ U(1) 的群结构
   
   ⚠️ 仍然开放（诚实标注）：
     - evolveFoldr_input / evolveFoldr_output 的归纳证明（留作 W2 练习）
     - causalLe 能否构造出格结构（⊔⊓）→ 需要更多结构假设
     - Fintype M → 独立假设，无法从 AxiomA/C 推出
   
   终极编译器状态：
     - CausalFromAlgebra.lean: 0 sorry / 0 error ✅
     - 整个 v12: 全量 lake build 待验证
   ═══════════════════════════════════════════════════════════ -/

end CSQIT.V12.CausalFromAlgebra
