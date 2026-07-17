import Mathlib.Data.List.Basic

example {α : Type*} (l1 l2 : List α) (i : ℕ) (h : i < l1.length) :
    (l1 ++ l2)[i] = l1[i] := by
  exact?
