import Mathlib.Data.List.Basic

structure CausalSite (M : Type*) where
  idx : ℕ
  out : M

def causalLT {M : Type*} (x y : CausalSite M) := x.idx < y.idx
def causalIncomparable {M : Type*} (x y : CausalSite M) :=
  ¬ causalLT x y ∧ ¬ causalLT y x

lemma causal_chain_pair_le {M : Type*} (x y : CausalSite M) :
    (causalLT x y ∨ causalIncomparable x y) ↔ x.idx ≤ y.idx := by
  simp only [causalLT, causalIncomparable]
  constructor
  · rintro (h1 | ⟨h2, h3⟩)
    · omega
    · omega
  · intro h
    by_cases hlt : x.idx < y.idx
    · left; exact hlt
    · right; constructor
      · exact hlt
      · omega

structure Weave {M : Type*} (L R : CausalSite M) where
  path : List (CausalSite M)
  path_nonempty : path ≠ []
  head_eq : path.head path_nonempty = L
  last_eq : path.getLast path_nonempty = R
  causal_chain : ∀ (i : ℕ) (hi : i + 1 < path.length),
    causalLT (path[i]'(by omega)) (path[i + 1]'(by omega)) ∨
    causalIncomparable (path[i]'(by omega)) (path[i + 1]'(by omega))

namespace Weave

def comp {M : Type*} {L MID R : CausalSite M} (w1 : Weave L MID) (w2 : Weave MID R) : Weave L R := by
  cases w1 with | mk w1_path w1_pne w1_head w1_last w1_cc =>
  cases w2 with | mk w2_path w2_pne w2_head w2_last w2_cc =>
  have h_pne : (w1_path ++ w2_path.tail) ≠ [] := by
    intro h; rw [List.append_eq_nil_iff] at h; exact w1_pne h.1
  have h_head : (w1_path ++ w2_path.tail).head h_pne = L := by
    cases w1_path with
    | nil => exact absurd rfl w1_pne
    | cons hd tl => exact w1_head
  have h_last : (w1_path ++ w2_path.tail).getLast h_pne = R := by
    cases w2_path with
    | nil => contradiction
    | cons hd tl =>
      simp [List.getLast_append, w2_last]
      <;> aesop
  have h_cc : ∀ (i : ℕ) (hi : i + 1 < (w1_path ++ w2_path.tail).length),
    causalLT ((w1_path ++ w2_path.tail)[i]'(by omega)) ((w1_path ++ w2_path.tail)[i + 1]'(by omega)) ∨
    causalIncomparable ((w1_path ++ w2_path.tail)[i]'(by omega)) ((w1_path ++ w2_path.tail)[i + 1]'(by omega)) := by
    intro i hi
    rw [causal_chain_pair_le]
    by_cases h : i + 1 < w1_path.length
    · -- Case 1: both in w1_path
      have h_i : i < w1_path.length := by omega
      have e1 : (w1_path ++ w2_path.tail)[i]'(by omega) = w1_path[i]'(by omega) :=
        List.getElem_append_left h_i
      have e2 : (w1_path ++ w2_path.tail)[i + 1]'(by omega) = w1_path[i + 1]'(by omega) :=
        List.getElem_append_left h
      rw [e1, e2]
      have h_cc := w1_cc i h
      rw [causal_chain_pair_le] at h_cc
      exact h_cc
    · by_cases h2 : i < w1_path.length
      · -- Junction: path[i] = w1_path.last = MID, path[i+1] = w2_path.tail[0]
        have e1 : (w1_path ++ w2_path.tail)[i]'(by omega) = w1_path[i]'(by omega) :=
          List.getElem_append_left h2
        have e2 : (w1_path ++ w2_path.tail)[i + 1]'(by omega) =
            w2_path.tail[i + 1 - w1_path.length]'(by omega) :=
          List.getElem_append_right (by omega : w1_path.length ≤ i + 1)
        rw [e1, e2]
        have h_zero : i + 1 - w1_path.length = 0 := by omega
        rw [h_zero]
        have h_w1_mid : w1_path[i]'(by omega) = MID := by
          have h_get := List.getLast_eq_getElem w1_pne
          rw [h_get] at w1_last
          have h_eq : w1_path.length - 1 = i := by omega
          rw [h_eq] at w1_last
          exact w1_last
        have h_tail_elem : w2_path.tail[0]'(by omega) = w2_path[1]'(by omega) := by
          exact List.getElem_tail (by omega)
        rw [h_w1_mid, h_tail_elem]
        have h_w2_mid : w2_path[0]'(by omega) = MID := by
          have h_get := List.head_eq_getElem w2_pne
          rw [h_get] at w2_head
          exact w2_head.symm
        rw [← h_w2_mid]
        have h_cc := w2_cc 0 (by omega)
        rw [causal_chain_pair_le] at h_cc
        exact h_cc
      · -- Both in w2_path.tail
        have e1 : (w1_path ++ w2_path.tail)[i]'(by omega) =
            w2_path.tail[i - w1_path.length]'(by omega) :=
          List.getElem_append_right (by omega : w1_path.length ≤ i)
        have e2 : (w1_path ++ w2_path.tail)[i + 1]'(by omega) =
            w2_path.tail[i + 1 - w1_path.length]'(by omega) :=
          List.getElem_append_right (by omega : w1_path.length ≤ i + 1)
        rw [e1, e2]
        have h_tail1 : w2_path.tail[i - w1_path.length]'(by omega) =
            w2_path[i - w1_path.length + 1]'(by omega) := by
          exact List.getElem_tail (by omega)
        have h_tail2 : w2_path.tail[i + 1 - w1_path.length]'(by omega) =
            w2_path[i + 1 - w1_path.length + 1]'(by omega) := by
          exact List.getElem_tail (by omega)
        rw [h_tail1, h_tail2]
        have h_cc := w2_cc (i - w1_path.length + 1) (by omega)
        rw [causal_chain_pair_le] at h_cc
        exact h_cc
  exact ⟨w1_path ++ w2_path.tail, h_pne, h_head, h_last, h_cc⟩

end Weave
