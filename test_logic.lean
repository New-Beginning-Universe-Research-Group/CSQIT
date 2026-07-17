-- 最小测试：验证降维打击修复的核心逻辑
-- causalLT L1 R1 与 causalIncomparable L1 R1 的矛盾

structure CausalSite (M : Type) where
  idx : Nat
  out : M

def causalLT {M : Type} (x y : CausalSite M) := x.idx < y.idx
def causalLE {M : Type} (x y : CausalSite M) := x.idx <= y.idx
def causalIncomparable {M : Type} (x y : CausalSite M) :=
  ¬ causalLT x y ∧ ¬ causalLT y x

-- 核心逻辑：causalLT L1 R1 蕴含 ¬causalIncomparable L1 R1
example {M : Type} (L1 R1 : CausalSite M) (h : causalLT L1 R1) :
    ¬ causalIncomparable L1 R1 := by
  intro h_incomp
  exact h_incomp.1 h

-- 验证：当 L1.idx < R1.idx 时，causalIncomparable L1 R1 = False
example {M : Type} (L1 R1 : CausalSite M) (h : L1.idx < R1.idx) :
    causalIncomparable L1 R1 = False := by
  simp [causalIncomparable, causalLT]
  exact h

-- 验证 h_cc 的核心引理：List.getElem_append_left 和 right
example : ∀ (l1 l2 : List Nat) (i : Nat) (h : i < l1.length),
    (l1 ++ l2)[i]'(by omega : i < (l1 ++ l2).length) = l1[i]'h := by
  intro l1 l2 i h
  exact List.getElem_append_left i h

example : ∀ (l1 l2 : List Nat) (i : Nat) (h : l1.length <= i),
    (l1 ++ l2)[i]'(by omega : i < (l1 ++ l2).length) = l2[i - l1.length]'(by omega) := by
  intro l1 l2 i h
  exact List.getElem_append_right l1 l2 i h
