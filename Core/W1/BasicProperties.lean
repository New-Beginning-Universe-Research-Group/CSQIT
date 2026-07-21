/-
CSQIT — 编织结构的基本性质
文件: Core/W1/BasicProperties.lean
版本: v11.2.4
日期: 2026-07-12

核心定理：Eckmann-Hilton 论证
  在满足 interchange 律的双幺半群中，
  两个幺半群运算必然相等且都是交换的。

这意味着：
  如果 seq 和 par 都是处处定义的二元运算，
  并且共享单位元、满足 interchange 律，
  那么 seq = par 且 seq 交换。

  换句话说：时间必然是交换的，时空必然合一。

  这是一个"不可能定理"——
  它告诉我们 v12 的原始公理框架（双幺半群）
  无法描述非交换的时间。

出路：操作需要有"边界"或"类型"，
  seq 和 par 都是部分定义的运算，
  这就是 2-范畴/幺半双范畴的框架。

-/

import Core.W3.Core
import Mathlib.Tactic

namespace CSQIT.W3

namespace BasicProperties

open Weave

variable {W : Type*} [Weave W]

/-! ============================================================================
   §1. 单位元的唯一性：skip = empty
   ============================================================================ -/

theorem seq_skip_skip_eq_empty :
    seq skip skip = (empty : W) := by
  have h := interchange (skip : W) empty empty skip
  simpa [par_left_empty, par_right_empty,
         seq_left_skip, seq_right_skip] using h

theorem empty_seq_right_id (x : W) :
    seq x empty = x := by
  have h1 : (empty : W) = seq skip skip := Eq.symm seq_skip_skip_eq_empty
  have h2 : seq x (seq skip skip) = seq (seq x skip) skip := Weave.seq_assoc x skip skip
  have h3 : seq (seq x skip) skip = seq x skip := by rw [seq_right_skip]
  have h4 : seq x skip = x := seq_right_skip x
  rw [h1, h2, h3, h4]

theorem empty_seq_left_id (x : W) :
    seq empty x = x := by
  have h1 : (empty : W) = seq skip skip := Eq.symm seq_skip_skip_eq_empty
  have h2 : seq (seq skip skip) x = seq skip (seq skip x) := (Weave.seq_assoc skip skip x).symm
  have h3 : seq skip (seq skip x) = seq skip x := by rw [seq_left_skip]
  have h4 : seq skip x = x := seq_left_skip x
  rw [h1, h2, h3, h4]

theorem skip_eq_empty :
    (skip : W) = empty := by
  have h1 : seq empty (skip : W) = skip := empty_seq_left_id (skip : W)
  have h2 : seq empty (skip : W) = empty := seq_right_skip (empty : W)
  rw [h2] at h1
  exact Eq.symm h1

/-! ============================================================================
   §2. skip = empty 的直接推论
   ============================================================================ -/

theorem par_skip_skip_eq_skip :
    par skip skip = (skip : W) := by
  have h1 : (skip : W) = empty := skip_eq_empty
  rw [h1]
  exact par_left_empty empty

theorem par_right_skip (x : W) :
    par x skip = x := by
  have h1 : (skip : W) = empty := skip_eq_empty
  rw [h1]
  exact par_right_empty x

theorem par_left_skip (x : W) :
    par skip x = x := by
  have h1 : (skip : W) = empty := skip_eq_empty
  rw [h1]
  exact par_left_empty x

/-! ============================================================================
   §3. Eckmann-Hilton 论证：seq = par 且 seq 交换
   ============================================================================ -/

private def f (x : W) : W := par skip x

theorem par_as_seq_via_f (x y : W) :
    seq (f x) (f y) = par x y := by
  dsimp only [f]
  have h := interchange (skip : W) x y (skip : W)
  simpa [par_left_empty, par_right_empty,
         seq_left_skip, seq_right_skip, par_comm] using h

theorem f_eq_id (x : W) : f x = x := by
  dsimp only [f]
  have h1 : (skip : W) = empty := skip_eq_empty
  rw [h1]
  exact par_left_empty x

/-- **Eckmann-Hilton 定理**：
    在满足 interchange 律的双幺半群中，
    两个幺半群运算相等。
    
    也就是说：seq x y = par x y 对所有 x, y 成立。
 -/
theorem seq_eq_par :
    ∀ (x y : W), seq x y = par x y := by
  intro x y
  have h1 : seq (f x) (f y) = par x y := par_as_seq_via_f x y
  have hx : f x = x := f_eq_id x
  have hy : f y = y := f_eq_id y
  rw [hx, hy] at h1
  exact h1

/-- **推论：seq 一定是交换的**
    
    因为 par 是交换的，而 seq = par，
    所以 seq 也是交换的。
    
    物理意义：
    如果时间复合是处处定义的，
    那么时间必然是交换的（可逆的、没有方向的）。
    
    但我们的物理世界中时间是有方向的、不可逆的。
    这说明：编织操作的时间复合不应该是处处定义的，
    操作应该有"边界"或"类型"，
    只有边界匹配的操作才能顺序复合。
 -/
theorem seq_comm :
    ∀ (x y : W), seq x y = seq y x := by
  intro x y
  have h1 : seq x y = par x y := seq_eq_par x y
  have h2 : par x y = par y x := par_comm x y
  have h3 : par y x = seq y x := (seq_eq_par y x).symm
  rw [h1, h2, h3]

/-! ============================================================================
   §4. 结论与展望
   
   我们证明了一个重要的"不可能定理"：
   
   如果编织操作的顺序复合和并行复合
   都是处处定义的二元运算，
   并且满足 interchange 律，
   那么它们必然相等并且都是交换的。
   
   这就是经典的 Eckmann-Hilton 论证。
   
   对我们的物理图景意味着什么？
   
   选项 A：时间确实是交换的、可逆的
     —— 但这和我们的直觉不符，
        而且无法解释时空分化。
   
   选项 B：操作有边界，复合是部分定义的
     —— 这是更自然的选择。
        编织操作有"输入端"和"输出端"，
        只有当输出端匹配输入端时才能顺序复合。
        这就是 2-范畴的框架。
   
   我们选择选项 B。
   
   在 2-范畴框架中：
   · 0-元（对象）：边界/位点/接口
   · 1-元（态射）：编织操作 f : a → b
   · seq（纵向复合）：f : a → b, g : b → c ⊢ seq f g : a → c
   · par（横向复合/张量积）：f : a → b, g : c → d ⊢ par f g : par a c → par b d
   · interchange 律：在类型匹配时成立
   
   因为运算只是部分定义的，
   Eckmann-Hilton 论证不适用，
   时间可以是非交换的，
   空间和时间可以真正区分开。
   
   这才是正确的框架。
   ============================================================================ -/

end BasicProperties

end CSQIT.W3
