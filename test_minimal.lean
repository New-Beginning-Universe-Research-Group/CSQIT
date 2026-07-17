-- 最小测试：验证 causalIncomparable X X 的行为
structure CausalSite (M : Type) where
  idx : Nat
  out : M

def causalLT {M : Type} (x y : CausalSite M) := x.idx < y.idx
def causalLE {M : Type} (x y : CausalSite M) := x.idx <= y.idx
def causalIncomparable {M : Type} (x y : CausalSite M) :=
  ¬ causalLT x y ∧ ¬ causalLT y x

-- 测试1：causalIncomparable X X = True
example {M : Type} (X : CausalSite M) : causalIncomparable X X = True := by
  simp [causalIncomparable, causalLT]

-- 测试2：¬causalIncomparable X X 是否可证明？
example {M : Type} (X : CausalSite M) : ¬ causalIncomparable X X := by
  simp [causalIncomparable, causalLT]
