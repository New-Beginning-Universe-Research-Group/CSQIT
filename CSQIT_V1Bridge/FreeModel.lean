/-
================================================================================
CSQIT_V1Bridge — 第二十四轮：见证模型的泛性质与 RG 像分类（G42）
模块: CSQIT_V1Bridge.FreeModel
版本: v0.1.0（2026-11-08）
================================================================================

上一轮（G41）停在「AxiomC 的幺半群刚性来自 comp_rule + 单射 + amp ≠ 0」。
本轮转向 V1 的「单生成元 + 组合」结构本身，回答一个此前只对自同态
（G21）回答过、对任意目标模型从未回答的问题：

  **从见证模型 (ℕ, a+b+1) 出发的同态有多少？它们的像是什么？**

结论（全部 A 档，零新增 axiom、零 sorry）：

  G42a  `composePow`：以 g 为生成元的组合幂序列
         `g¹ = g`, `g^(n+2) = g^(n+1) ∘ g`。
  G42b  幂的加法公式 `g^(a+b+1) = g^a ∘ g^b`（结合律，纯 AxiomA）。
  G42c  **泛性质（分类）**：任意 `φ : ℕ → C` 满足
         `φ (a+b+1) = φ a ∘ φ b`
         当且仅当 `φ n = (φ 0)^(n+1)`（逐点）。
         即同态完全由 `φ 0` 决定——`Hom(见证模型, C) ≃ C`。
  G42d  每个 `g : C` 都实现一个同态（存在性方向）。
  G42e  **振幅层的单参数形式**：若目标承载 AxiomC，则沿任意同态
         `amp (φ n) = amp (φ 0)^(n+1)`。
  G42f  **RG 像的二分（否定式）**：若同态 `φ` 不是单射，则它的像
         是周期的（存在 d > 0 使 `φ (n+d) = φ n`），因而是有限像。
         等价地：**从见证模型出发的无穷像 RG 流必为单射**。

结构性含义：

  1. 见证模型 `(ℕ, a+b+1)` 是「单生成元自由半群」在 v23 签名下的
     具体实现：`n ↦ n+1` 把它同构到 `(ℕ⁺, +)`，而 v23 的 compose
     只保留结合律。因此 V1 的「复合链 / operad 单生成元」不是额外
     结构，它就是 v23 的自由对象。
  2. RG 流（compose-同态）在 v23 中的像被一个元素完全钉死；这与
     G21（自同态分类 `φ n = φ 0 + n(φ 0+1)`）互为特例/一般化。
  3. G42f 给出 RG 的信息损失判据：丢信息的流只能落在有限载体上，
     无限载体上的流必为嵌入。这与 G36「保振幅粗粒化必为双射」
     互补——那里限制振幅，这里不限振幅、只限制像的基数。

判定档位：A（可证；composePow 是定义性构造，不是新增公设）。
纪律：零新增 axiom、零 sorry；不修改 CSQIT_W1 / CSQIT_Enhanced /
      既有 V1Bridge 文件；只新增本文件与 lakefile 一行 root。
依赖：CSQIT_V1Bridge.LayerWitness（→ … → AxiomA/AxiomC 定义与
      见证模型实例）。
================================================================================ -/

import CSQIT_V1Bridge.LayerWitness

namespace CSQIT_V1Bridge

open CSQIT_W1.CompilerAxioms
open CSQIT_W1.Foundation

/-! ============================================================================
    §1. 组合幂：定义与基本恒等式
   ============================================================================ -/

/-- **组合幂（定义）**：`composePow A g 0 = g`，
    `composePow A g (n+1) = compose (composePow A g n) g`。

    语义：把 `g` 连续组合 `n+1` 次（`g¹, g², g³, …`）。
    选择这个下标约定，是为了让短语「见证模型的元素 n 对应 g^(n+1)」
    在 G42c 中不出现偏移。 -/
def composePow {M C : Type*} (A : AxiomA M C) (g : C) : ℕ → C
  | 0 => g
  | n + 1 => A.compose (composePow A g n) g

/-- `composePow` 的零位展开（定义性，`rfl`）。 -/
theorem composePow_zero {M C : Type*} (A : AxiomA M C) (g : C) :
    composePow A g 0 = g := rfl

/-- `composePow` 的递归展开（定义性，`rfl`）。 -/
theorem composePow_succ {M C : Type*} (A : AxiomA M C) (g : C) (n : ℕ) :
    composePow A g (n + 1) = A.compose (composePow A g n) g := rfl

/-- **G42b（A 档）**：组合幂的加法公式
    `g^(a+b+1) = g^a ∘ g^b`。

    证明只用结合律：对 `b` 归纳；`b = 0` 时两边都是 `g^(a+1)`；
    归纳步把 `g^((a+b+1)+1)` 展开为 `g^(a+b+1) ∘ g`，再用归纳
    假设与结合律把 `(g^a ∘ g^b) ∘ g` 重排成 `g^a ∘ g^(b+1)`。 -/
theorem composePow_add {M C : Type*} (A : AxiomA M C) (g : C) :
    ∀ a b : ℕ,
      composePow A g (a + b + 1) = A.compose (composePow A g a) (composePow A g b) := by
  intro a b
  induction b with
  | zero =>
      -- a + 0 + 1 = a + 1
      show composePow A g (a + 1) = A.compose (composePow A g a) (composePow A g 0)
      rw [composePow_succ, composePow_zero]
  | succ b ih =>
      -- a + (b+1) + 1 = (a + b + 1) + 1
      have hstep : a + (b + 1) + 1 = (a + b + 1) + 1 := by omega
      rw [hstep, composePow_succ, ih, A.compose_assoc, ← composePow_succ]

/-! ============================================================================
    §2. G42c：泛性质——任意同态由 φ 0 决定
   ============================================================================ -/

/-- **G42c-1（A 档，主分类）**：设 `φ : ℕ → C` 满足
    `φ (a+b+1) = φ a ∘ φ b`，则 `φ n = (φ 0)^(n+1)`。

    证明：令 `g = φ 0`。递推式 `φ (n+1) = φ n ∘ φ 0`（取 `a = n, b = 0`）
    说明 `φ` 就是 `composePow A g`；对 `n` 归纳即可。
    关键点：证明只用到「同态等式 + 结合律」，不需要交换律、单位元、
    振幅层或有限性。 -/
theorem witnessHom_classification {M C : Type*} (A : AxiomA M C)
    (φ : ℕ → C) (h : ∀ a b : ℕ, φ (a + b + 1) = A.compose (φ a) (φ b)) :
    ∀ n : ℕ, φ n = composePow A (φ 0) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have hstep : φ (n + 1) = A.compose (φ n) (φ 0) := by
        have h0 := h n 0
        simpa using h0
      rw [hstep, ih, composePow_succ]

/-- **G42c-2（A 档，双向）**：同态等式与「φ 为某个组合幂序列」等价。

    (→) 即 G42c-1；(←) 由 G42b 的加法公式直接给出。 -/
theorem witnessHom_iff_composePow {M C : Type*} (A : AxiomA M C) (φ : ℕ → C) :
    (∀ a b : ℕ, φ (a + b + 1) = A.compose (φ a) (φ b)) ↔
      (∀ n : ℕ, φ n = composePow A (φ 0) n) := by
  constructor
  · intro h n
    exact witnessHom_classification A φ h n
  · intro h a b
    rw [h (a + b + 1), h a, h b, composePow_add]

/-- **G42d（A 档，存在性）**：任意 `g : C` 都实现一个从见证模型出发的同态，
    且该同态把 `0` 送到 `g`。

    这与 G42c 合起来给出 `Hom(见证模型, C) ≃ C`：同态的集合与载体的
    元素一一对应。 -/
theorem exists_witnessHom_of_element {M C : Type*} (A : AxiomA M C) (g : C) :
    ∃ φ : ℕ → C,
      (∀ a b : ℕ, φ (a + b + 1) = A.compose (φ a) (φ b)) ∧ φ 0 = g := by
  refine ⟨composePow A g, ?_, rfl⟩
  intro a b
  exact composePow_add A g a b

/-- **G42d′（A 档，唯一性）**：两个同态若在 `0` 处相等，则作为函数相等。
    这是 `Hom(见证模型, C) ≃ C` 的单射性一半。 -/
theorem witnessHom_unique_of_zero {M C : Type*} (A : AxiomA M C)
    {φ ψ : ℕ → C}
    (hφ : ∀ a b : ℕ, φ (a + b + 1) = A.compose (φ a) (φ b))
    (hψ : ∀ a b : ℕ, ψ (a + b + 1) = A.compose (ψ a) (ψ b))
    (h0 : φ 0 = ψ 0) : φ = ψ := by
  funext n
  rw [witnessHom_classification A φ hφ n, witnessHom_classification A ψ hψ n, h0]

/-! ============================================================================
    §3. G42e：目标承载 AxiomC 时，振幅沿同态是单参数指数
   ============================================================================ -/

/-- **G42e-1（A 档）**：组合幂的振幅是生成元振幅的整数幂
    `amp (g^(n+1)) = amp(g)^(n+1)`。由 `comp_rule` 对 `n` 归纳。 -/
theorem composePow_amplitude {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (g : C) (n : ℕ) :
    Cx.amplitude (composePow A g n) = (Cx.amplitude g) ^ (n + 1) := by
  induction n with
  | zero => simp [composePow_zero]
  | succ n ih =>
      have h1 : Cx.amplitude (composePow A g (n + 1)) =
          (Cx.amplitude g) ^ (n + 1) * Cx.amplitude g := by
        rw [composePow_succ, Cx.comp_rule, ih]
      rw [h1]
      exact (pow_succ (Cx.amplitude g) (n + 1)).symm

/-- **G42e（A 档）**：任意从见证模型出发的同态，在目标 AxiomC 模型上的
    振幅满足 `amp (φ n) = amp (φ 0)^(n+1)`。

    这是 V1「复振幅 e^{iS}」在 v23 中的单参数形式：沿一条 RG 流，
    振幅完全由生成元的相位决定；配合 `actionPhase_add`，
    作用量也满足 `S (φ n) = (n+1) • S (φ 0)`（Angle 的加法形式）。 -/
theorem witnessHom_amplitude {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (φ : ℕ → C) (hφ : ∀ a b : ℕ, φ (a + b + 1) = A.compose (φ a) (φ b))
    (n : ℕ) :
    Cx.amplitude (φ n) = (Cx.amplitude (φ 0)) ^ (n + 1) := by
  rw [witnessHom_classification A φ hφ n, composePow_amplitude]

/-! ============================================================================
    §4. G42f：RG 像的二分——非单射同态只有有限像
   ============================================================================ -/

/-- **G42f（A 档，否定式）**：若从见证模型出发的同态 `φ`（目标承载
    AxiomC）不是单射，则存在 `d > 0` 使 `φ (n+d) = φ n` 对一切 `n` 成立。

    机制：非单射给出 `φ m = φ n`（`m < n`）。由 G42e，
    `amp(φ 0)^(m+1) = amp(φ 0)^(n+1)`；振幅非零，消去得
    `amp(φ 0)^(n-m) = 1`。于是对任意 `k`，
    `amp(φ (k+d)) = amp(φ 0)^(k+d+1) = amp(φ 0)^(k+1) = amp(φ k)`，
    再由振幅单射得 `φ (k+d) = φ k`。

    语义：**无限载体上的 RG 流必为单射**；会丢信息的流只能落在
    有限（周期）像上。与 G36（保振幅粗粒化 ⇒ 双射）互补。 -/
theorem witnessHom_not_injective_periodic {M C : Type*} [A : AxiomA M C] [Cx : AxiomC M C]
    (φ : ℕ → C) (hφ : ∀ a b : ℕ, φ (a + b + 1) = A.compose (φ a) (φ b))
    (hnot : ¬ Function.Injective φ) :
    ∃ d : ℕ, 0 < d ∧ ∀ n : ℕ, φ (n + d) = φ n := by
  -- 非单射给出两个不同原像，排序后记为 m < n
  rw [Function.Injective] at hnot
  push_neg at hnot
  obtain ⟨m, n, hmn, hlt⟩ : ∃ m n : ℕ, φ m = φ n ∧ m < n := by
    obtain ⟨m, n, hmn, hne⟩ := hnot
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨m, n, hmn, h⟩
    · exact ⟨n, m, hmn.symm, h⟩
  -- 振幅幂相等
  have hexp : (Cx.amplitude (φ 0)) ^ (m + 1) = (Cx.amplitude (φ 0)) ^ (n + 1) := by
    rw [← witnessHom_amplitude (A := A) (Cx := Cx) φ hφ m,
      ← witnessHom_amplitude (A := A) (Cx := Cx) φ hφ n, hmn]
  -- 消去得 (amp (φ 0))^(n-m) = 1
  have hd : (Cx.amplitude (φ 0)) ^ (n - m) = 1 := by
    have h2 : (Cx.amplitude (φ 0)) ^ (m + 1) =
        (Cx.amplitude (φ 0)) ^ (m + 1) * (Cx.amplitude (φ 0)) ^ (n - m) := by
      calc
        (Cx.amplitude (φ 0)) ^ (m + 1)
            = (Cx.amplitude (φ 0)) ^ (n + 1) := hexp
        _ = (Cx.amplitude (φ 0)) ^ ((m + 1) + (n - m)) := by
              rw [show n + 1 = (m + 1) + (n - m) by omega]
        _ = (Cx.amplitude (φ 0)) ^ (m + 1) *
              (Cx.amplitude (φ 0)) ^ (n - m) := pow_add _ _ _
    have h' : (Cx.amplitude (φ 0)) ^ (m + 1) * 1 =
        (Cx.amplitude (φ 0)) ^ (m + 1) * (Cx.amplitude (φ 0)) ^ (n - m) := by
      rw [mul_one]
      exact h2
    exact (mul_left_cancel₀ (pow_ne_zero (m + 1) (amplitude_ne_zero (φ 0))) h').symm
  refine ⟨n - m, by omega, ?_⟩
  intro k
  apply Cx.amplitude_injective
  rw [witnessHom_amplitude (A := A) (Cx := Cx) φ hφ (k + (n - m)),
    witnessHom_amplitude (A := A) (Cx := Cx) φ hφ k]
  have hcalc : (Cx.amplitude (φ 0)) ^ (k + (n - m) + 1) =
      (Cx.amplitude (φ 0)) ^ (k + 1) := by
    rw [show k + (n - m) + 1 = (k + 1) + (n - m) by omega, pow_add, hd, mul_one]
  rw [hcalc]

/-! ============================================================================
    §5. 汇总（G42）

  新增结论（全部 A 档、零新增公设、零 sorry）：

    G42a  composePow：单生成元组合幂序列
    G42b  加法公式 g^(a+b+1) = g^a ∘ g^b
    G42c  泛性质：同态 ⟺ φ n = (φ 0)^(n+1)；Hom(见证, C) ≃ C
    G42d  存在性 + 由 φ 0 决定的唯一性
    G42e  目标 AxiomC 时 amp (φ n) = amp(φ 0)^(n+1)
    G42f  非单射同态必为周期（有限像）；无限像流必单射

  与既有结论的关系：

    · G21（自同态分类）是本模块在 C = ℕ、A = witnessAxiomA 上的特例
      （`φ n = φ 0 + n(φ 0+1)` 与 `composePow` 的算术展开一致）。
    · G24（witness-compose 上 AxiomC 的振幅参数化 `c^(n+1)`）是
      G42e 在同一模型上的特例。
    · G36（保振幅满射 ⇒ 双射）与 G42f 互补：前者限制「保振幅」，
      后者限制「像的基数」；两者共同刻画 RG 流的信息损失边界。
   ============================================================================ -/

end CSQIT_V1Bridge
