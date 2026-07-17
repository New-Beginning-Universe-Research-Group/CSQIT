-- 最小测试：验证 List.getElem_append_left/right 的用法

-- 测试 getElem_append_left
example (l1 l2 : List Nat) (i : Nat) (h1 : i < l1.length) :
    (l1 ++ l2)[i] = l1[i] := by
  rw [List.getElem_append_left]
  -- 需要 i < l1.length，已有 h1

-- 测试 getElem_append_right
example (l1 l2 : List Nat) (i : Nat) (h1 : l1.length <= i) (h2 : i < (l1 ++ l2).length) :
    (l1 ++ l2)[i] = l2[i - l1.length] := by
  rw [List.getElem_append_right]
  -- 需要 l1.length <= i，已有 h1

-- 测试组合：getElem_append_left 后 getElem_append_right
example (l1 l2 : List Nat) (i : Nat)
    (h1 : i < l1.length) (h2 : l1.length <= i + 1) (h3 : i + 1 < (l1 ++ l2).length) :
    (l1 ++ l2)[i] = l1[i] ∧ (l1 ++ l2)[i+1] = l2[i+1 - l1.length] := by
  constructor
  · rw [List.getElem_append_left]
  · rw [List.getElem_append_right]
