/-
================================================================================
CSQIT 10.4.5 - AxiomD 独立性证明
文件: Core/AxiomD_Independence.lean
版本: 10.4.5 (Canonical Textbook Edition)
日期: 2026-06-18
================================================================================
-/

import Core.Axioms
import Core.Theorems
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic

namespace CSQIT.AxiomD_Independence

open CSQIT

inductive TestC | a | b | c

instance : DecidableEq TestC :=
  fun x y =>
    match x, y with
    | TestC.a, TestC.a => isTrue rfl
    | TestC.b, TestC.b => isTrue rfl
    | TestC.c, TestC.c => isTrue rfl
    | TestC.a, TestC.b => isFalse (fun h => by cases h)
    | TestC.a, TestC.c => isFalse (fun h => by cases h)
    | TestC.b, TestC.a => isFalse (fun h => by cases h)
    | TestC.b, TestC.c => isFalse (fun h => by cases h)
    | TestC.c, TestC.a => isFalse (fun h => by cases h)
    | TestC.c, TestC.b => isFalse (fun h => by cases h)

inductive TestM | m0 | m1

instance : DecidableEq TestM :=
  fun x y =>
    match x, y with
    | TestM.m0, TestM.m0 => isTrue rfl
    | TestM.m1, TestM.m1 => isTrue rfl
    | TestM.m0, TestM.m1 => isFalse (fun h => by cases h)
    | TestM.m1, TestM.m0 => isFalse (fun h => by cases h)

def testM_le (x y : TestM) : Prop :=
  match x, y with
  | TestM.m0, TestM.m0 => True
  | TestM.m0, TestM.m1 => True
  | TestM.m1, TestM.m0 => False
  | TestM.m1, TestM.m1 => True

def testM_lt (x y : TestM) : Prop :=
  match x, y with
  | TestM.m0, TestM.m0 => False
  | TestM.m0, TestM.m1 => True
  | TestM.m1, TestM.m0 => False
  | TestM.m1, TestM.m1 => False

theorem axiomD_independent_of_AB :
  ∃ (M C : Type) (instA : AxiomA M C) (instB : AxiomB M C),
    ∃ (α β : C),
      (instB.lt (instA.output α) (instA.output β)) ∧
      (¬ ∃ (γ : C), instA.compose α γ = β) := by
  let M := TestM
  let C := TestC
  
  let input : C → List M := fun _ => []
  
  let output : C → M := fun
    | TestC.a => TestM.m0
    | TestC.b => TestM.m1
    | TestC.c => TestM.m1
  
  let compose : C → C → C := fun α β =>
    match β with
    | TestC.a => TestC.a
    | TestC.b => TestC.b
    | TestC.c => TestC.b
  
  have input_nodup : ∀ α : C, (input α).Nodup := by
    intro α
    exact List.nodup_nil
  
  have compose_input : ∀ α β : C, input (compose α β) = input α ++ input β := by
    intro α β
    rfl
  
  have compose_output : ∀ α β : C, output (compose α β) = output β := by
    intro α β
    cases β
    rfl
    rfl
    rfl
  
  have compose_assoc : ∀ α β γ : C, compose (compose α β) γ = compose α (compose β γ) := by
    intro α β γ
    cases β <;> cases γ <;> rfl
  
  let instA : AxiomA M C := {
    input := input,
    output := output,
    input_nodup := input_nodup,
    compose := compose,
    compose_input := compose_input,
    compose_output := compose_output,
    compose_assoc := compose_assoc
  }
  
  let le := testM_le
  let lt := testM_lt
  
  have le_refl : ∀ x : M, le x x := by
    intro x; cases x <;> trivial
  
  have le_trans : ∀ x y z : M, le x y → le y z → le x z := by
    intro x y z hxy hyz
    cases x <;> cases y <;> cases z <;> trivial
  
  have le_antisymm : ∀ x y : M, le x y → le y x → x = y := by
    intro x y hxy hyx
    cases x <;> cases y <;> trivial
  
  have le_m0_m0 : le TestM.m0 TestM.m0 := trivial
  have le_m1_m1 : le TestM.m1 TestM.m1 := trivial
  
  have lt_iff_le_not_le : ∀ x y : M, lt x y ↔ (le x y ∧ ¬ le y x) := by
    intro x y
    cases x
    case m0 =>
      cases y
      case m0 =>
        exact Iff.intro (fun h => False.elim h) (fun h => absurd le_m0_m0 h.2)
      case m1 =>
        exact Iff.intro (fun _ => ⟨trivial, fun h => h⟩) (fun _ => trivial)
    case m1 =>
      cases y
      case m0 =>
        exact Iff.intro (fun h => False.elim h) (fun h => False.elim h.1)
      case m1 =>
        exact Iff.intro (fun h => False.elim h) (fun h => absurd le_m1_m1 h.2)
  
  have localFinite_past : ∀ x : M, Set.Finite {y : M | lt y x} := by
    intro x
    cases x
    case m0 =>
      have : {y : M | lt y TestM.m0} = ∅ := by
        ext y
        cases y
        case m0 => exact Iff.intro (fun h => False.elim h) (fun h => False.elim h)
        case m1 => exact Iff.intro (fun h => False.elim h) (fun h => False.elim h)
      rw [this]
      exact Set.finite_empty
    case m1 =>
      have : {y : M | lt y TestM.m1} = {TestM.m0} := by
        ext y
        cases y
        case m0 => exact Iff.intro (fun _ => Set.mem_singleton TestM.m0) (fun h => by trivial)
        case m1 => exact Iff.intro (fun h => False.elim h) (fun h => False.elim (by rw [Set.mem_singleton_iff] at h; cases h))
      rw [this]
      exact Set.finite_singleton TestM.m0

  have localFinite_future : ∀ x : M, Set.Finite {y : M | lt x y} := by
    intro x
    cases x
    case m0 =>
      have : {y : M | lt TestM.m0 y} = {TestM.m1} := by
        ext y
        cases y
        case m0 => exact Iff.intro (fun h => False.elim h) (fun h => False.elim (by rw [Set.mem_singleton_iff] at h; cases h))
        case m1 => exact Iff.intro (fun _ => Set.mem_singleton TestM.m1) (fun h => by trivial)
      rw [this]
      exact Set.finite_singleton TestM.m1
    case m1 =>
      have : {y : M | lt TestM.m1 y} = ∅ := by
        ext y
        cases y
        case m0 => exact Iff.intro (fun h => False.elim h) (fun h => False.elim h)
        case m1 => exact Iff.intro (fun h => False.elim h) (fun h => False.elim h)
      rw [this]
      exact Set.finite_empty
  
  have weaving_axiom : ∀ (α : C) (x : M), x ∈ instA.input α → lt x (instA.output α) := by
    intro α x hx
    cases α <;> cases x <;> cases hx
  
  let instB : AxiomB M C := {
    le := le,
    lt := lt,
    le_refl := le_refl,
    le_trans := le_trans,
    le_antisymm := le_antisymm,
    lt_iff_le_not_le := lt_iff_le_not_le,
    localFinite_past := localFinite_past,
    localFinite_future := localFinite_future,
    weaving_axiom := weaving_axiom
  }
  
  have h_lt : instB.lt (instA.output TestC.a) (instA.output TestC.c) := by
    have oa : instA.output TestC.a = TestM.m0 := rfl
    have oc : instA.output TestC.c = TestM.m1 := rfl
    rw [oa, oc]
    exact trivial
  
  have h_not_exists : ¬ ∃ (γ : C), instA.compose TestC.a γ = TestC.c := by
    intro h
    cases h with
    | intro γ hγ =>
      cases γ
      have : instA.compose TestC.a TestC.a = TestC.a := rfl
      rw [this] at hγ
      exact absurd hγ (by decide : TestC.a ≠ TestC.c)
      have : instA.compose TestC.a TestC.b = TestC.b := rfl
      rw [this] at hγ
      exact absurd hγ (by decide : TestC.b ≠ TestC.c)
      have : instA.compose TestC.a TestC.c = TestC.b := rfl
      rw [this] at hγ
      exact absurd hγ (by decide : TestC.b ≠ TestC.c)
  
  exact ⟨M, C, instA, instB, TestC.a, TestC.c, h_lt, h_not_exists⟩

def axiomD_independent_of_ABC : Prop :=
  ∃ (M C : Type) (instA : AxiomA M C) (instB : AxiomB M C) (_ : AxiomC M C),
    ∃ (α β : C),
      (instB.lt (instA.output α) (instA.output β)) ∧
      (¬ ∃ (γ : C), instA.compose α γ = β)

end CSQIT.AxiomD_Independence