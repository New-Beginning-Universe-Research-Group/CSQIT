/-
================================================================================
CSQIT_WeaveBridge.WeaveCore
按 v11.2.8 `Core/WeavingStructure.lean` 重建 CausalSite / Weave / length /
trivial / weaveComplexity。归档只读；本文件不引入任何新公理、不含 sorry。

重建清单（归档行号 → 本文件对应项）：
  CausalSite               :33-37
  causalLT / causalLE      :43 / :45
  causalIncomparable       :51-52
  structure Weave          :66-77（五字段逐条，无省略）
  Weave.length             :82
  Weave.trivial            :85-91
  weaveComplexity          :142-148

环境限制（必须记录）：
  本项目 `lean-toolchain` pin 为 `leanprover/lean4:v4.29.0-rc6`，本机 elan 未安装
  该版本，尝试联网拉取失败（github.com:443 超时）；本机仅有 `v4.29.1`，用它重建
  Mathlib 会在 `Mathlib/Tactic/Translate/Core.lean:448` 报 `Unknown identifier
  exceptEmoji`。因此本文件刻意**不 import Mathlib**，只用 Lean 核心库：
  - `weaveComplexity` 在归档是 ℝ 值（L142-148）；本文件落码为等价的 Nat 骨架
    `weaveComplexityNat`，ℝ 版本见 §4 注释。
================================================================================ -/

namespace CSQIT_WeaveBridge

universe u

/-! ============================================================================
   §1. 因果位点（归档 L33-37）
   ============================================================================ -/

/-- **因果位点**：`idx` 为位点标识，`out` 为输出关系元。 -/
structure CausalSite (M : Type u) where
  /-- 位点标识 -/
  idx : Nat
  /-- 位点的输出关系元 -/
  out : M

/-- 严格因果序（归档 L43）。 -/
def causalLT {M : Type u} (x y : CausalSite M) : Prop := x.idx < y.idx

/-- 非严格因果序（归档 L45）。 -/
def causalLE {M : Type u} (x y : CausalSite M) : Prop := x.idx ≤ y.idx

/-- 因果不可比（归档 L51-52）。 -/
def causalIncomparable {M : Type u} (x y : CausalSite M) : Prop :=
  ¬ causalLT x y ∧ ¬ causalLT y x

/-! ============================================================================
   §2. 编织路径（归档 L66-77，五字段逐条）
   ============================================================================ -/

/-- **编织路径**：从 L 到 R 的路径，每步为严格因果序或因果不可比。 -/
structure Weave {M : Type u} (L R : CausalSite M) where
  /-- 路径序列 -/
  path : List (CausalSite M)
  /-- 路径非空 -/
  path_nonempty : path ≠ []
  /-- 路径从 L 开始 -/
  head_eq : path.head path_nonempty = L
  /-- 路径到 R 结束 -/
  last_eq : path.getLast path_nonempty = R
  /-- 因果链约束 -/
  causal_chain : ∀ (i : Nat) (hi : i + 1 < path.length),
    causalLT (path.get ⟨i, Nat.lt_of_succ_lt hi⟩) (path.get ⟨i + 1, hi⟩) ∨
      causalIncomparable (path.get ⟨i, Nat.lt_of_succ_lt hi⟩) (path.get ⟨i + 1, hi⟩)

namespace Weave

/-- 编织路径的长度（归档 L82）。 -/
def length {M : Type u} {L R : CausalSite M} (w : Weave L R) : Nat := w.path.length

/-- 平凡编织路径：单点路径（归档 L85-91）。 -/
def trivial {M : Type u} (α : CausalSite M) : Weave α α :=
  ⟨[α], List.cons_ne_nil α [], rfl, by simp, by
    intro i hi
    exfalso
    have h1 : i + 1 < 1 := hi
    exact Nat.not_succ_le_zero i (Nat.le_of_lt_succ h1)⟩

end Weave

/-! ============================================================================
   §3. 编织复杂度（归档 L142-148 的 Nat 骨架）
   ============================================================================ -/

/-- **编织复杂度（Nat 骨架）**：`n ≤ 1` 时为 0，否则为边数 `n - 1`。

    归档定义（L142-148）为 ℝ 值：
    `let n := w.length; if n ≤ 1 then 0 else (n - 1 : ℝ)`。
    Nat 骨架与之一一对应，仅值域不同。 -/
def weaveComplexityNat {M : Type u} {L R : CausalSite M} (w : Weave L R) : Nat :=
  let n := w.length
  if n ≤ 1 then 0 else n - 1

/-- 平凡路径复杂度为零（归档文档 L139 声明，此处补证）。 -/
theorem weaveComplexityNat_trivial {M : Type u} (s : CausalSite M) :
    weaveComplexityNat (Weave.trivial s) = 0 := by
  unfold weaveComplexityNat Weave.trivial Weave.length
  simp

/-! ============================================================================
   §4. 未落码项（逐条给位置与原因，不用"篇幅"作理由）

   A. `weaveComplexity : ℝ`（归档 L142-148）
      Lean 核心库无 ℝ；ℝ 版本需要 `Mathlib.Data.Real.Basic`，而本环境的工具链
      缺口（见文件头）使任何 Mathlib 依赖都无法编译。已用 §3 的 Nat 骨架替代。

   B. `Weave.comp`（归档 L94-118）
      归档 `causal_chain` 分支直接给出 `exact w2.causal_chain (i - n1) h_shift'`
      （L117），但目标里的 `path.get` 是拼接表 `w1.path ++ w2.path.tail` 上的取值，
      必须先经 `List.getElem_append_left/right` 改写，不能直接 `exact`。
      且拼接点错位：当 `i + 1 = w1.path.length` 时，该步是
      `(w1.path.getLast, w2.path[1])`，对应 `w2.causal_chain 0`；
      归档传的 `i - w1.path.length` 在该点虽为 0，但在 `i ≥ w1.path.length` 时
      需要的却是 `i - w1.path.length + 1`，两个分支不能共用一个索引。
      精确重建需按 `i + 1 < n1` / `i + 1 = n1` / `i ≥ n1` 三分支重写。
      本轮不落半成品，故删去该定义，也不保留 sorry。

   C. `weaveBandGap`（归档 L180-186）
      定义体含 `inverseFineStructure / observerBridge`，来自归档 import 的
      `Unified.Constants.FineStructure` 与 `Unified.Constants.CrossConsistency`。
      这两个模块不在 v23 工作区；重建必须新造常量或立公设，与"零新增 axiom"
      冲突，故不落码。
   ============================================================================ -/

end CSQIT_WeaveBridge
