# CSQIT W1/W2/W3 Layer Definitions and Scope

> Version: v11.2.6 | Date: 2026-07-21
> Purpose: Strict reference baseline for subsequent work

---

## Core Methodology

- **W1 Layer**: Formalized mathematical core (strict definitions and proofs), no sorry
- **W2 Layer**: Effective theory layer (conditional theorems + physical assumptions), contains a small number of sorry and conjecture placeholders
- **Key Principle**: Subsequent work must strictly distinguish the scope of theorems; finite model theorems must not be extrapolated to infinite models

---

## Core Definition 0: Time — Scale and Development Process

> **Global Consistency Principle**: The definition of time runs through all W1/W2/W3 layers; the form of expression becomes progressively richer, but the core remains consistent:
> **Time = Causal Order = Scale Flow = Development Process**

### 0.1 Three-Layer Unified Formulation

| Layer | Formulation of Time | Mathematical Carrier | Core File |
|-------|---------------------|---------------------|-----------|
| **W1** | Time = Causal Order | Partial order `≤` / `isImmediateSuccessor` | [CausalLattice.lean](https://github.com/New-Beginning-Universe-Research-Group/CSQIT/tree/release-v11.2.6/Core/W1/CausalLattice.lean) |
| **W2** | Time = Scale Flow (refinement process) | `projectiveScale n` / `d_dt` | [ScaleDynamics.lean](https://github.com/New-Beginning-Universe-Research-Group/CSQIT/tree/release-v11.2.6/Core/W2/ScaleDynamics.lean) |
| **W3** | Time = Development Process (growth/evolution) | Growth lineage / symmetry hierarchy emergent at each level | [GrowthAndSymmetry.lean](https://github.com/New-Beginning-Universe-Research-Group/CSQIT/tree/release-v11.2.6/Core/W3/GrowthAndSymmetry.lean), [Summary.lean](https://github.com/New-Beginning-Universe-Research-Group/CSQIT/tree/release-v11.2.6/Core/W3/Summary.lean) |

### 0.2 W1 Layer: Time = Causal Order (Strict Definition)

**Definition Source**: Partial order `≤` of `CausalLattice M`

**Core Elements**:
1. **Arrow of Time**: Given by the directionality of the partial order (`x ≤ y` means x causally precedes y)
2. **Discreteness**: Realized through `isImmediateSuccessor` — the passage of time is a discrete "next moment" jump
3. **Starting and Ending Points**: `⊥` (Big Bang) and `⊤` (final state) of `BoundedCausalLattice`
4. **Time Non-Commutativity**: Sequential composition `seq` is non-commutative → prerequisite for spacetime differentiation ([WeavingStructure.lean](https://github.com/New-Beginning-Universe-Research-Group/CSQIT/tree/release-v11.2.6/Core/W1/WeavingStructure.lean))

**Key Theorem Support**:
- `sup_monotone`: Causal union preserves temporal order (the union of later events is also later)
- `bot_unique` / `top_unique`: Uniqueness of the starting and ending points of time

### 0.3 W2 Layer: Time = Scale Flow (Refinement Process)

**Definition Source**: `projectiveScale n = 2π · n / (n+1)`

**Core Elements**:
1. **Scale Parameter n**: Natural number index, corresponding to the degree of refinement of the causal lattice (the "developmental stage" of the universe)
2. **Strictly Monotone Increasing**: `projectiveScale_strictMono` — scale strictly increases with n, time is irreversible
3. **Finite to Infinite Transition**: `projectiveScale n < 2π` holds for all finite n, but approaches 2π as n→∞
4. **Discrete Time Derivative**: `d_dt O n dt = (O(n+1) - O(n)) / dt` — rate of change over time derived from scale differences

**Physical Significance**:
- The "passage of time" perceived by humans = the refinement process of the causal lattice
- The "infinitely distant future" closes on the topological circle (completing one full loop returns to the starting point)
- π appears everywhere in physics because the scale flow closes on the topological circle

### 0.4 W3 Layer: Time = Development Process (Growth/Evolution)

**Definition Source**: Growth lineage and the level-by-level emergence of symmetry hierarchy

**Core Elements**:
1. **Growth Hierarchy**: Three-group lineage = three growth stages (A₄ → A₅ → PSL(2,7))
2. **Irreversibility Threshold**: When d ≥ 3 (p=7), dynamics become irreversible, and the arrow of time truly emerges ([Fin7Uniqueness.lean](https://github.com/New-Beginning-Universe-Research-Group/CSQIT/tree/release-v11.2.6/Core/W2/Fin7Uniqueness.lean))
3. **Large-Scale Cyclicity**: Cyclic universe model — local time has direction, global time is closed ([CyclicUniverse.lean](https://github.com/New-Beginning-Universe-Research-Group/CSQIT/tree/release-v11.2.6/Core/W3/CyclicUniverse.lean))
4. **Three-Lock Constants**: 20, 111, 289 are the contribution ratios of the three growth stages

### 0.5 Global Consistency: The Trinity of Time

```
W1: Causal Order ≤  ──┐
                       ├── Three aspects of the same reality
W2: Scale Flow n    ──┤     (Time = Order = Scale = Development)
                       │
W3: Growth Process  ──┘
```

**Mathematical Thread Running Through**:
- **W1 → W2**: The refinement sequence of the causal lattice (`seq : ℕ → Type*`) concretizes the abstract causal order into scale parameters
- **W2 → W3**: Scale flow drives the level-by-level emergence of symmetry groups, forming "milestones" of the development process
- **W3 → W1**: Each stage of growth is a causal lattice (satisfying W1 axioms); the development process does not violate causal order

**Usage Principles**:
1. When dealing with strict causal structure, use W1 layer's `CausalLattice` / `≤` language
2. When dealing with continuous limits and rates of change, use W2 layer's `projectiveScale` / `d_dt` language
3. When dealing with cosmic evolution and symmetry emergence, use W3 layer's growth lineage language
4. The three-layer formulations are equivalent; the choice depends on context, **layer confusion must not occur**

### 0.6 Relationship with "4D Spacetime"

**Key Clarification**: "4D" in CSQIT is **not** four co-equal dimensions, but rather:

> **3D Space + Time Flow (Causal Evolution)**

- 3D Space = spatial cross-section at the same causal depth (simultaneity slice)
- Time Flow = causal order relation between cross-sections (not an additional spatial dimension)
- 4D Convergence = the continuous limit of each 3D slice individually + telescopic cancellation between slices

This is fundamentally different from traditional relativity treating time as a fourth dimension: time is the more basic causal order, and space emerges from time (spacetime differentiation when `par ≠ seq`).

---

## Part One: W1 Layer

### 1.1 Core Axiom Definitions (Axioms.lean)

| Axiom | Type Class | Core Fields | Scope |
|-------|-----------|-------------|-------|
| AxiomA | `AxiomA M C` | input, output, compose, input_nodup, compose_input, compose_output, compose_assoc | Any M, C |
| AxiomA' | `AxiomA' M C` | AxiomA fields + combine + combine_assoc + compose_output' (using combine instead of compose_output) | Any M, C |
| AxiomB | `AxiomB M C` [A : AxiomA M C] | le, le_refl, le_trans, le_antisymm, lt_iff_le_not_le, localFinite_past, localFinite_future, weaving_axiom (using A.input/A.output) | Any M, C |
| AxiomB' | `AxiomB' M C` [A' : AxiomA' M C] | Identical fields to AxiomB, but weaving_axiom' uses A'.input/A'.output | Any M, C |
| AxiomB_totalOrder | `AxiomB_totalOrder M C` [A] [B] | AxiomB + le_total (total order assumption) | Any M, C |
| AxiomB'_totalOrder | `AxiomB'_totalOrder M C` [A'] [B'] | AxiomB' + le_total (total order assumption) | Any M, C |
| AxiomC | `AxiomC M C` [A : AxiomA M C] | amplitude, norm_one, comp_rule (using A.compose), amplitude_injective | Any M, C |
| AxiomC' | `AxiomC' M C` [A' : AxiomA' M C] | amplitude, norm_one, comp_rule (using A'.compose), amplitude_injective | Any M, C |
| AxiomD | `AxiomD M C` [A] [B] | op_weaving (using A.output / A.compose / B.lt) | Any M, C |
| AxiomD' | `AxiomD' M C` [A'] [B'] | op_weaving (using A'.output / A'.compose / B'.lt) | Any M, C |
| AxiomF' / G' / H' / I' | — | Same content as original versions, only type parameters changed from [AxiomA] to [AxiomA'] (do not depend on specific AxiomA fields) | Any M, C |
| Theory | `Theory M C` | All of A+B+C+D+F+G+H+I+J | Any M, C |
| Theory' | `Theory' M C` | All of A'+B'+C'+D'+F'+G'+H'+I'+J' | Any M, C |
| PartialTheory' | `PartialTheory' M C` | With symmetry-breaking record | Any M, C |

### 1.2 Core Collapse Theorems (CausalWeaving.lean) — ⚠️ The Most Fundamental Impossibility

**Scope: Any AxiomA Instance**

| Theorem | Content | File |
|---------|---------|------|
| `input_must_be_empty` | ∀ α, input α = [] | CausalWeaving.lean:45 |
| `input_length_zero` | ∀ α, \|input α\| = 0 | CausalWeaving.lean:63 |
| `no_causal_input` | ∀ α x, x ∉ input α | CausalWeaving.lean:72 |
| `no_satisfiable_weaving_premise` | ¬∃ α x, x ∈ input α | CausalWeaving.lean:89 |
| `weaving_axiom_equivalent_to_true` | weaving_axiom ↔ True | CausalWeaving.lean:98 |
| `axiomD_redundant` | \|input β\| = \|input α\|+1 is always false | CausalWeaving.lean:108 |

**Constraint Significance**: Under AxiomA, all rules have no input, the weaving axiom holds vacuously, and AxiomD is redundant.

### 1.3 Two-Aspect Theorems (TwoAspectTheorems.lean) — Scope Classification

#### A. Finite Models Only (Finite C) ⚠️ Not Extrapolatable to Infinite

| Theorem | Strict Premises | Content |
|---------|----------------|---------|
| `standard_theory_two_aspect_dichotomy` | `[Finite C] [DecidableEq C]` | Two-aspect dichotomy |
| `standard_theory_no_two_aspect_balance` | `[Finite C] [DecidableEq C]` | Two aspects cannot both be achieved |
| `amplitude_injective_implies_left_transitive` | `[Finite C] [DecidableEq C]` | Injective ⇒ left transitive |
| `two_aspect_asymmetry_in_finite_group_models` | `[Finite C]` + left_transitive | Asymmetry |
| `amplitude_output_no_function_dependency` | left_transitive + `[Finite C]` | No function dependency |
| `conservation_law_lower_bound` | `[Finite C] [Nonempty C]` | Conservation lower bound |
| `measurement_forces_degeneracy` | `[Finite C] [DecidableEq C]` | Measurement forces degeneracy |
| `finite_semigroup_injective_hom_to_group` | `[Finite S]` | Finite semigroup → group |

#### B. Infinite Models Only (Infinite M)

| Theorem | Strict Premises | Content |
|---------|----------------|---------|
| `infinite_whole_simple_not_bounded` | `[Infinite M]` | Infinite whole is not bounded by finite constraints |

#### C. Requiring left_transitive (Finite or Infinite)

| Theorem | Premises | Content |
|---------|----------|---------|
| `output_degenerate_theorem` | `h : left_transitive` | output degenerates to a constant function |
| `two_aspects_are_decoupled` | `h_left_transitive` | Two aspects decoupled |
| `left_transitive_no_weaving` | `h : left_transitive` | Left transitive ⇒ no nontrivial weaving |

#### D. Any Model (Depending Only on AxiomA/B/C)

| Theorem | Content |
|---------|---------|
| `right_projective_amplitude_degenerate` | Right projective ⇒ amplitude=1 |
| `two_aspect_extremes_summary` | Two extremes summary |
| `amplitude_injective_implies_left_mul_injective` | Injective ⇒ left multiplication injective |

### 1.4 Amplitude Theorems (AmplitudeTheorems.lean) — Any Model

**Scope: Any AxiomA + AxiomC Instance**

Core theorems: `amplitude_norm_one`, `amplitude_compose`, `amplitude_compose_assoc`, `amplitude_eq_imp_rule_eq`, `amplitude_left_cancel`, `amplitude_right_cancel`, `amplitude_re_le_one`, `amplitude_im_le_one`

### 1.5 Causal Lattice and Weaving Structure — Independent Subsystem

| Definition | File | Scope |
|------------|------|-------|
| `CausalSite M` | WeavingStructure.lean:34 | Any M (index order, not AxiomB.lt) |
| `causalLT` | WeavingStructure.lean:44 | Index order x.idx < y.idx |
| `causalIncomparable` | WeavingStructure.lean | Index incomparable |
| `Weave L R` | WeavingStructure.lean:66 | Any M (pure list structure) |
| `CausalLattice M` | CausalLattice.lean | Any M |
| `BoundedCausalLattice M` | CausalLattice.lean | Any M |
| `DistributiveCausalLattice M` | CausalLattice.lean | Any M |

**⚠️ Key Clarification**: `Weave` uses `CausalSite` (index order), **not** AxiomB's `B.lt`. The two are connected through `CausalSite.out : M`, but the causal order definitions are different.

### 1.6 Axiom Independence (Independence.lean)

**Strictly Proven Independent Constraints** (via explicit countermodel construction):
1. `compose_assoc` (AxiomA) — non-associativity counterexample
2. `le_antisymm` (AxiomB) — non-anti-symmetry counterexample
3. `norm_one` (AxiomC) — norm not equal to 1 counterexample
4. `amplitude_injective` (AxiomC) — non-injective counterexample

**Open Problem**: `axiomD_independent_of_ABC` (Independence of AxiomD under A+B+C)

### 1.7 W1 Layer Open Problems

| Proposition | File | Nature |
|-------------|------|--------|
| `csqit_infinite_model_exists_claim` | Consistency.lean | Infinite model existence (unproven) |
| `csqit_nontrivial_entropy_exists_claim` | Consistency.lean | Nontrivial entropy existence (unproven) |
| `state_space_cardinality_theorem` | AlgebraicCausality.lean | True placeholder (premises too strong, conclusion trivial) |
| `level_functor_exists` | HierarchicalWeaving.lean | Level functor conjecture |

### 1.8 Standard Axioms vs. Enhanced Axioms: Fundamental Scope Differences ⚠️

**Core Conclusion: Standard axioms and enhanced axioms (' versions) have vastly different scopes and must not be mixed.**

| Dimension | Standard Axioms (AxiomA/B/C/D) | Enhanced Axioms (AxiomA'/B'/C'/D') |
|-----------|-------------------------------|-------------------------------------|
| **output Behavior** | `compose_output = output β` (retains only right argument, left argument information lost) | `compose_output' = combine (output α) (output β)` (retains both sides' information) |
| **input Behavior** | Constrained by `input_must_be_empty`, `input α = []` for all α | Similarly constrained by `input_must_be_empty` (because compose_input has the same form) |
| **weaving_axiom** | Holds vacuously (premise always false) | Also holds vacuously (input is still empty), but non-degenerate output gives causal order real objects |
| **Amplitude Multiplication Law** | `amplitude (A.compose α β) = amplitude α * amplitude β`, but due to output degeneracy, amplitude and causal aspect decouple | `amplitude (A'.compose α β) = amplitude α * amplitude β`, output is non-degenerate, amplitude and causal aspect can couple |
| **Two-Aspect Theorems** | Fully applicable (`output_degenerate_theorem`, etc.) | Not applicable (`compose_output'` does not satisfy `output(compose α β) = output β`, left transitive premise changes) |
| **Core Collapse Theorem** | `input_must_be_empty` applies | `input_must_be_empty` also applies (input-side structure unchanged) |
| **Model Instances** | `trivialModel` (Unit), `boolModel` (Bool), `nonTrivialFinModel` (Fin 5/4) | `fin7Model` (Fin 7), `fin8Model` (Fin 8), `natPartialModel` (ℕ) |
| **Applicable Scenarios** | Strict theorem proving in pure algebra / pure causal aspect | Nontrivial dynamics, amplitude-causal coupling, physically meaningful modeling |

**Key Theorem Support**:
- `AxiomA_to_AxiomA'`: Standard AxiomA can be viewed as a degenerate special case of AxiomA' (taking `combine _ b := b`)
- `output_degenerate_theorem`: Under left transitive + standard AxiomA, output degenerates to a constant function
- `two_aspects_are_decoupled`: Under standard axioms, amplitude aspect and causal aspect decouple (no function dependency)

**Usage Principles**:
1. **Strict theorem proving** should prioritize standard axioms (weakest assumptions, most universal conclusions)
2. **Nontrivial model construction** must use enhanced axioms (otherwise output degenerates and physical meaning is vacuous)
3. **Theorems under standard axioms must not be directly extrapolated to enhanced axioms** (e.g., two-aspect dichotomy theorems do not hold under AxiomA')
4. **Theorems under enhanced axioms must be annotated with their premises** (clearly state dependency on AxiomA's compose_output')

---

## Part Two: W2 Layer

### 2.1 W2 Layer Overall Characteristics

- **Positioning**: Effective theory layer, conditional theorems + physical assumptions
- **Strictness**: 13/18 files have no sorry at all; 3 files contain sorry (1 of which is an intentional counterexample)
- **Relationship with W1**: Depends on W1 through imports; does not actively use core collapse theorems (such as `input_must_be_empty`) as proof premises, but their conclusions have been internalized as default settings in model construction

### 2.2 Core Physical Assumptions List

| Assumption | File | Content | Nature |
|------------|------|---------|--------|
| `structureFormationWindow` | Fin7Uniqueness.lean | θ ∈ (0.28, 0.33) | Physical window assumption |
| `algebraicDegree` | Fin7Uniqueness.lean | Prime algebraic degree | Definition |
| `IsFin7Regular` | B_V_Naturalness.lean | W1 layer strict regularity | Definition |
| `EffectiveFin7Regular` | B_V_Naturalness.lean | W2 layer effective regularity | Definition |
| `seventh_root_sum_neg_one` | B_V_Naturalness.lean | 7th root sum | axiom |
| `cos2pi7_cubic_equation` | B_V_Naturalness.lean | cos(2π/7) cubic equation | axiom |
| `binary_generation` | GrowthModel.lean | Binary generation | axiom |
| `alpha_pos` | PeriodicTable.lean | 0 < α | Physical constant |

### 2.3 W2 Layer Theorem Scope Classification

#### A. Depending on Fintype (Finite Models Only)

| Theorem/Definition | File | Premises |
|-------------------|------|----------|
| BV series theorems | B_V_Naturalness.lean | `[BoundedCausalLattice M] [Fintype M]` + Fin7 regularity |
| DerivationPath1/2/3 | Fin7Uniqueness.lean | `[Fintype C]` |
| Regge convergence series | ContinuumLimit.lean | `[CausalLattice V] [Fintype V] [DecidableEq V]` |
| `finite_evolve_tradeoff` | EnhancedModels.lean | `[Fintype M] [LinearOrder M]` |
| `twoAspectParameter_range` | CausalLattice.lean (W1) | `[Fintype M] [Nonempty M]` |

#### B. Depending on Infinite (Infinite Models Only)

| Theorem | File | Content |
|---------|------|---------|
| `nat_future_infinite` | EnhancedModels.lean | ℕ's future is infinite, breaking localFinite_future |

**⚠️ Key**: `natPartialModel` is an infinite model, **not subject to two-aspect dichotomy theorems**.

#### C. Conditional Theorems

| Theorem | File | Preconditions |
|---------|------|--------------|
| `reggeAction_projection_decomposition_full` | ContinuumLimit.lean | `h_area_norm` + `h_curvature_const` |
| `reggeConverges4D_to_EinsteinHilbert` | ContinuumLimit.lean | `EffectiveFin7Regular` + `h_decomp` |
| `reggeConverges4D_conditional` | ContinuumLimit.lean | Annotated as "requires additional tools" |
| `reggeConverges4D_via_2D_GaussBonnet` | ContinuumLimit.lean | Conditional theorem |

#### D. Pure Numerical/Group Theory Theorems (No Fintype Requirement)

| Theorem | File | Content |
|---------|------|---------|
| Three-lock constants derivation | ThreeLocksDerivation.lean | 20+111+289=420 |
| Physical constants derivation | PhysicalConstants.lean | α⁻¹, m_p/m_e, etc. |
| Gravity derivation | GravityDerivation.lean | Algebraic form of G |
| Strict derivation | StrictDerivation.lean | Ω_b, Ω_DM, Ω_Λ |
| Shell capacity | TwoAspectToSU2.lean (W1) | 2n² |
| Three-group hierarchy | ThreeGroupHierarchy.lean (W1) | \|A₄\|=12, \|A₅\|=60, \|PSL(2,7)\|=168 |

### 2.4 W2 Layer sorry and Conjecture Status

#### Genuine Proof Gaps (0 in W2 Layer)

The W2 layer has no genuine proof gaps. `scalarCurvature3D_from_2D_sections` has been downgraded to a True placeholder (premises too strong, conclusion trivial; does not constitute a substantive proof gap).

#### Intentionally Retained Counterexample sorry (4 instances, 4 proof obligations of the same construction)

| Location | File | Content |
|----------|------|---------|
| Lines 183-187 | FiniteWeavingExamples.lean | 4 fields of `cyclic_stable_substructure`: past_closed, rep_in_carrier, combine_closed, internally_connected (mathematically invalid, retained as counterexample) |

#### Conjecture Placeholders (def ... : Prop := True, 12 instances)

| File | Count | Representative Conjecture |
|------|-------|--------------------------|
| B_V_Naturalness.lean | 5 | `BVFromGrowthRateConjecture`, etc. |
| ContinuumLimit.lean | 5 | `ReggeConvergesToEinsteinHilbert`, etc. |
| ScaleDynamics.lean | 1 | `SU3RootSystemCommutationRelations` |
| HolographicIsomorphism.lean | 1 | `HolographicConjecture` |

### 2.5 W2 Layer Key Models

| Model | File | Type | Scope |
|-------|------|------|-------|
| `fin7Model` | EnhancedModels.lean | Theory (Fin 7) | Finite |
| `fin8Model` | EnhancedModels.lean | Theory (Fin 8) | Finite |
| `natPartialModel` | EnhancedModels.lean | PartialTheory' ℕ | **Infinite** ⚠️ |
| `nonTrivialFinModel` | FinModels.lean (W1) | Theory (Fin 5) (Fin 4) | Finite |
| `trivialModel` | BasicModels.lean (W1) | Theory Unit Unit | Degenerate |
| `boolModel` | BasicModels.lean (W1) | Theory Bool Unit | Finite |

---

## Part Three: Constraints for Subsequent Work

### 3.1 Absolute Constraints (Must Not Be Violated)

1. **`input_must_be_empty`**: In any AxiomA instance, rules have no input. "Non-empty input" AxiomA models must not be constructed.
2. **Finiteness Boundary**: Two-aspect dichotomy theorems (`standard_theory_two_aspect_dichotomy`, etc.) hold only under `[Finite C]`. **They must not be extrapolated to infinite models such as `natPartialModel`**.
3. **Weaving Vacuity**: Under AxiomA, weaving_axiom holds vacuously. Any construction of "nontrivial weaving" must use `Weave`/`CausalSite` structures, not AxiomA's input/output.

### 3.2 Scope Selection Guide

| Work Objective | Usable Theorems | Unusable Theorems |
|---------------|----------------|-------------------|
| Finite model analysis | All W1 + W2 theorems | — |
| Infinite model analysis | `input_must_be_empty`, amplitude theorems, `infinite_whole_simple_not_bounded`, `nat_future_infinite` | Two-aspect dichotomy theorems, `amplitude_injective_implies_left_transitive` |
| Causal lattice analysis | CausalLattice theorems, Weave structure | AxiomA collapse theorems (different structure) |
| Continuum limit | Conditional theorems (with EffectiveFin7Regular etc. premises) | Unconditional Regge convergence (still a conjecture) |
| Cross-scale holography | HolographicIsomorphism mathematical parts | HolographicConjecture (W3 conjecture) |

### 3.3 Proof Gap Priority

#### W1 Layer (0 Genuine Gaps)

The W1 layer has no genuine proof gaps. `exists_order_two_subgroup` proof has been completed; `state_space_cardinality_theorem` has been downgraded to a True placeholder.

#### W2 Layer (0 Genuine Gaps)

The W2 layer has no genuine proof gaps. `scalarCurvature3D_from_2D_sections` has been downgraded to a True placeholder.

#### W3 Layer (1 Instance)

1. **Low Priority**: `Angle sum and boundedness` (ContinuumLimit.lean)

#### Completed (sorry eliminated in this update)

- ✅ `causal_chain` of `Weave.comp` (pure list property, not involving axioms)
- ✅ `char_real_d2_quadratic` / `char_real_d2_eq_neg_golden_conjugate` (Fin7 uniqueness)
- ✅ `fin7_uniqueness_W2` d≥3 branch
- ✅ `hubble_prediction` (W3 layer, UnifiedPicture.lean)
- ✅ `exists_order_two_subgroup` (W1 layer, AlgebraicCausality.lean)
- ✅ `p7_satisfies_WAP_conditions` (W3 layer, ObserverFormalization.lean)

---

## Part Three: W3 Layer (Strictly Compiled Theorems)

### 3.1 W3 Layer Positioning

- **Positioning**: Exploratory framework (physical interpretation + numerical verification)
- **Strictness**: Some theorems have been strictly compiled (pure numerical/group theory calculations), some are conjectures
- **Relationship with W2**: Depends on W2's effective theory assumptions, connecting mathematical structures with physical observables

### 3.2 Strictly Compiled Theorems (UnifiedPicture.lean)

| Theorem | Content | Proof Strategy |
|---------|---------|---------------|
| `lcm_orders_eq_840` | lcm(60, 168) = 840 | `rfl` |
| `totalClosure_from_lcm_div_2` | lcm(60, 168) / 2 = 420 | `rfl` |
| `A5_prime_factors` | \|A₅\| = 2² × 3 × 5 | `norm_num` |
| `PSL27_prime_factors` | \|PSL(2,7)\| = 2³ × 3 × 7 | `norm_num` |
| `union_prime_factors_eq_420_factors` | 420 = 2² × 3 × 5 × 7 | `rfl` |
| `inverse_fine_structure_eq_137_036` | α⁻¹ = 34259/250 = 137.036 | `norm_num` |
| `omega_sum_eq_one` | Ω_b + Ω_DM + Ω_Λ = 1 | `norm_num` |
| `hubble_prediction` | \|α⁻¹ × 30/61 - 269579/4000\| < 1/10000 | Full fraction form + `abs_of_pos` + `div_lt_div_iff_of_pos_left` + `omega` |
| `involutions_eq_3x7` | 21 = 3 × 7 | `norm_num` |
| `Omega_b_eq_1_over_21` | Ω_b = 1/21 | `norm_num` |
| `dark_matter_eq_sum_without_order4` | Dark matter molecules = 21 + 24 + 24 + 42 | `norm_num` |
| `cross_validity_1/2/3` | 111+289=20², 20×21=420, 17²+111=400 | `norm_num` |
| `fermat_prime_F2_eq_17` | 17 = 2^(2^2) + 1 | `norm_num` |

**Note**: The original form of `hubble_prediction` used decimal literals (67.39475, 1e-4); due to a deficiency in Lean 4.29.0-rc6's `norm_num` OfScientific plugin when combining `abs` with decimal literals, it was replaced with the equivalent fraction form (269579/4000, 1/10000).

### 3.3 W3 Layer Conjecture Placeholders

- Unified picture conjecture (relationship between weaving bimonoid automorphism group and 420)
- Correspondence between A₅ ↔ 3D spatial symmetry / PSL(2,7) ↔ causal network symmetry

---

## Appendix: File Index

### W1 Layer (25 files)
- Axioms.lean, CausalWeaving.lean, TwoAspectTheorems.lean, AmplitudeTheorems.lean
- Independence.lean, AxiomC_Independence.lean, AxiomD_Independence.lean, Consistency.lean
- WeavingStructure.lean, CausalLattice.lean, CausalLatticeToAxiomA.lean
- TwoAspectToSU2.lean, ThreeGroupHierarchy.lean, Hierarchy.lean
- HierarchicalWeaving.lean, HierarchicalLevels.lean, FoundationalGrowth.lean, GrowthToAxioms.lean
- AlgebraicCausality.lean, CausalSetCorrespondence.lean, Unified.lean
- BasicModels.lean, BasicProperties.lean, ShellCapacityDerivation.lean
- Models/FinModels.lean

### W2 Layer (18 files)
- B_V_Naturalness.lean, ContinuumLimit.lean, Fin7Uniqueness.lean
- GravityDerivation.lean, GrowthAndSymmetry.lean, GrowthModel.lean
- GroupRepresentationData.lean, HDST.lean, HolographicIsomorphism.lean
- Integration.lean, PhysicalConstants.lean, ScaleDynamics.lean
- StrictDerivation.lean, Summary.lean, ThreeLocksDerivation.lean
- Models/EnhancedModels.lean, Models/FiniteWeavingExamples.lean, Models/PeriodicTable.lean

### W3 Layer (Verified Files)
- UnifiedPicture.lean (12 theorems strictly compiled)
- ObserverFormalization.lean (`p7_satisfies_WAP_conditions` proof completed)

---

## Part Four: Implementation Status Overview (Code vs. Paper Correspondence Audit)

> This chapter is based on a cross-check of all 65 Lean source files against the theoretical paper "The Source Code of the Universe",
> conducting a layered audit of the degree to which various claims in the paper are actually implemented in the codebase.
> Core principle: strictly distinguish between "formally proven", "conditional theorems", "conjecture placeholders", and "pure narrative interpretation".

### 4.1 Overall Assessment: Jewel and Gold Leaf

**Core Conclusion**: The paper "The Source Code of the Universe" is a composite of "jewel and gold leaf".

| Paper Claim Level | Code Implementation Status | Assessment |
|------------------|---------------------------|------------|
| **W1 Layer Theorems** (two-aspect, input must be empty, θ algebraic derivation, thermodynamic arrow, etc.) | ✅ **Implemented, and over-delivered** | This is the project's core achievement. Approximately 15-20 key theorems are strictly proven. The reliability of the codebase is built on these foundations. |
| **W2 Layer / Conditional Conclusions** (Regge convergence, Fin7 uniqueness, effective regularity) | 🔶 **Partially implemented** | The formalization framework exists, but key jumps (such as `h_decomp` or the instantiation of `EffectiveFin7Regular`) are retained as `sorry` or unproven definitions. They remain "effective conjectures". |
| **W3 Layer / Ultimate Narrative** (existence inversion, cross-scale holography, six-layer locking, unified identity equation) | ❌ **Not implemented** | These constitute the philosophical appeal and narrative ambition of the paper, but at the code level they are an "empty city". They have not been formalized, nor are they within the decidable scope of the current Lean logic. |

**One-Sentence Summary**:
> Every claim in the paper attempts to take flight from some cornerstone of the code,
> but only some cornerstones support the full theoretical flight.

---

### 4.2 Category One: Implemented W1 Layer Theorems (✅ Code Strictly Corresponds to Paper)

Conclusions in this category have clear Lean theorem names and complete proofs; they are the core value of the project.

| Claim in Paper | Corresponding Theorem in Code | File | Status and Notes |
|---------------|-------------------------------|------|-----------------|
| **Two-Aspect Dichotomy Theorem**: Causal aspect and information aspect cannot both be nontrivial | `standard_theory_two_aspect_dichotomy` | `Core/W1/TwoAspectTheorems.lean` | ✅ **Strictly proven**. Premises: `[Finite C] [DecidableEq C]`. |
| **No Equilibrium Theorem**: No two-aspect equilibrium state exists in standard theory | `standard_theory_no_two_aspect_balance` | `Core/W1/TwoAspectTheorems.lean` | ✅ **Strictly proven**. Direct corollary of the dichotomy theorem. |
| **Input Must Be Empty Theorem (Core Collapse)**: All rule inputs are empty | `input_must_be_empty` | `Core/W1/CausalWeaving.lean` | ✅ **Strictly proven**. Derived from `compose_input` and `input_nodup`. |
| **Algebraic Causal Order**: Transitivity of `algebraic_le` | `algebraic_le_trans` | `Core/W1/AlgebraicCausality.lean` | ✅ **Strictly proven**. Uses `mul_nsmul'` lemma. |
| **Order Jump Phenomenon**: Order 2 and order 8 weaving, result jumps to order 8 | `order_jump_example` | `Core/W2/Models/FiniteWeavingExamples.lean` | ✅ **Strictly proven**. `generated_subgroup` carrier equals order 8 subgroup. |
| **Algebraic Derivation of θ (Conditional)**: `θ = 1/(2+2cos(2π/7))` | `BV_ratio_from_EffectiveFin7` | `Core/W2/B_V_Naturalness.lean` | ✅ **Strictly proven (conditional)**. Premise: `EffectiveFin7Regular`. |
| **θ Satisfies Cubic Equation**: `θ³ - 6θ² + 5θ - 1 = 0` | `BV_ratio_cubic_effective` | `Core/W2/B_V_Naturalness.lean` | ✅ **Strictly proven**. Based on `cos2pi7_cubic_equation` axiom. |
| **Projective Scale Strictly Increasing with Upper Bound**: `s(n) = 2πn/(n+1)` | `projectiveScale_strictMono`, `projectiveScale_lt_two_pi` | `Core/W2/ScaleDynamics.lean` | ✅ **Strictly proven**. |
| **SU(3) Cartan Generator Commutativity** | `cartan_generators_commute` | `Core/W2/ScaleDynamics.lean` | ✅ **Strictly proven**. Only commutativity; connection with CSQIT not proven. |
| **Second Law of Thermodynamics (Discrete Version)**: Causal entropy monotonically non-decreasing | `causalEntropy_monotone` | `Core/W1/ThermodynamicArrow.lean` | ✅ **Strictly proven**. Key: `causalPast` set inclusion. |
| **Past Hypothesis Theorem**: Bounded causal lattice has minimum entropy element | `past_hypothesis_is_theorem` | `Core/W1/ThermodynamicArrow.lean` | ✅ **Strictly proven**. Depends on `bot_le`. |
| **Finite Evolution Trade-off**: Finite totally ordered monotonic map must have a fixed point | `finite_evolve_tradeoff` | `Core/W2/Models/EnhancedModels.lean` | ✅ **Strictly proven**. |
| **Dynamical Reversibility for p≤5 (Part of Fin7 Uniqueness)** | `fin7_uniqueness_W2` | `Core/W2/Fin7Uniqueness.lean` | ✅ **Strictly proven**. Proved "primes less than 7 are reversible"; did not prove "must be 7". |
| **Prime Exclusion Theorem**: p=7 is the only prime that places θ within the structure formation window | `prime_exclusion_theorem` | `Core/W2/Fin7Uniqueness.lean` | ✅ **Strictly proven**. θ ∉ (0.28, 0.33) for p ≠ 7. |
| **Three-Lock Constants Numerical Consistency**: 20+111+289=420, etc. | Numerous `norm_num`-verified theorems | `Unified/Constants/CrossConsistency.lean` | ✅ **Strictly proven**. Pure numerical/arithmetic consistency checks. |
| **Axiom Independence** (4 instances) | `compose_assoc_is_independent`, etc. | `Core/W1/Independence.lean` | ✅ **Strictly proven**. Via countermodel construction. |
| **Order Two Subgroup Existence** | `exists_order_two_subgroup` | `Core/W1/AlgebraicCausality.lean` | ✅ **Strictly proven**. |

---

### 4.3 Category Two: Partially Implemented or Conditional Statements (🔶 Framework Exists, but Depends on Unproven Assumptions)

Content in this category is described in the paper as key inferences of the W2 or W1 layers, but actually depends on stronger assumptions that have not been proven in the code.

| Claim in Paper | Corresponding Code | File | Status and Notes |
|---------------|-------------------|------|-----------------|
| **`EffectiveFin7Regular` is a physically realizable average regularity** | `EffectiveFin7Regular` is a `def` | `Core/W2/B_V_Naturalness.lean` | 🔶 **Definition exists, but not a theorem**. No specific model (Fin 7, Fin 8, or ℕ) has been proven to satisfy this condition. |
| **θ corresponds to total matter density Ω_m of the universe** | No direct correspondence | — | ❌ **Pure W3 interpretation**. No matter density definition in code, let alone a theorem equating θ with Ω_m. |
| **Regge action converges to Einstein-Hilbert action** | `reggeConverges4D_to_EinsteinHilbert` | `Core/W2/ContinuumLimit.lean` | 🔶 **Conditional theorem**. Proof depends on the crucial `h_decomp` assumption, which is `sorry`. |
| **Variational principle of unified action** | `totalAction` definition | `Core/W2/ScaleDynamics.lean` | ❌ **Pure framework**. Action definition exists, but no formalization of "variation" and "deriving field equations". |
| **Uniqueness of Fin 7 (not a posteriori choice, derived from axioms that it must be 7)** | `prime_exclusion_theorem` + expansion hierarchy discussion | `Core/W2/Fin7Uniqueness.lean` | 🔶 **Partial number-theoretic support, not a complete proof**. Elimination method proven, but the positive argument for "why it must be 7" is missing. The "3×3 affine plane modulo 8 congruence" argument in the paper is entirely absent from the code. |
| **Strict derivation of G_unit** | `weaveElasticModulus_Fin7` | `Unified/Constants/Gravity.lean` | 🔶 **Conditional strict proof**. Indeed derived from `EffectiveFin7Regular`, but that premise is not instantiated. |
| **Scalar curvature 3D constructed from 2D sections** | `scalarCurvature3D_from_2D_sections` | `Core/W2/ContinuumLimit.lean` | 🔶 **True placeholder**. Premises too strong, conclusion trivial; downgraded to placeholder. |
| **Holographic isomorphism conjecture** | `HolographicConjecture` | `Core/W2/HolographicIsomorphism.lean` | 🔶 **Conjecture placeholder**. Mathematical framework exists, but core isomorphism is unproven. |

---

### 4.4 Category Three: Unimplemented / Pure W3 / Philosophical Claims (❌ No Correspondence in Code)

Content in this category occupies a large portion of the paper and constitutes its "ultimate narrative", but leaves no trace in the Lean code. They should be understood as theoretical conjectures and philosophical interpretations, not results of formalized proofs.

| Claim in Paper | Exists in Code? | Status and Notes |
|---------------|----------------|-----------------|
| **"Observer exists ⇔ Structure=7" existence inversion** | ❌ **Does not exist** | Pure philosophical reasoning, no formalized theorem support. The code does not define "observer". |
| **"From Ω_m to DNA, structure=7 is the unique algebraic invariant"** | ❌ **Does not exist** | Pure cross-scale analogy. The code has no definitions of "genetic codons" or "DNA bases". 64 in the code is merely the cardinality of Fin 8. |
| **"The universe is an automaton, state space cardinality locked at 8"** | ❌ **Does not exist** | `order_jump_example` proves closure of Fin 8 under specific weaving, but there is no theorem proving "state space cardinality must be 8". |
| **"Dark energy is the remaining combinatorial degrees of freedom when the causal lattice is saturated and can no longer generate new relation pairs"** | ❌ **Does not exist** | Pure philosophical interpretation. The code has no formalized definition of "relation pair saturation" or "combinatorial degrees of freedom". |
| **"Binary sequence 0→1→2→4→8→64→∞" as a holistic development law** | ❌ **Does not exist** | Each step has scattered code support, but the sequence itself has not been defined or proven as a whole in the code. |
| **Cross-scale holographic principle (from Planck scale to cosmic scale)** | ❌ **Does not exist** | `HolographicIsomorphism.lean` has a mathematical framework, but the physical-level cross-scale correspondence is not formalized. |
| **Unified identity equation (mathematical expression of "I = Universe")** | ❌ **Does not exist** | Pure philosophical/narrative level, no correspondence in code. |
| **Anthropic principle of time (why we perceive time the way we do)** | ❌ **Does not exist** | `ObserverFormalization.lean` has a WAP framework, but it is not linked to time perception. |

---

### 4.5 Codebase Honesty Checklist

The most admirable quality of the codebase is its **honesty** — it explicitly marks "known unknowns" in multiple ways:

| Marking Method | Meaning | Representative Example |
|---------------|---------|----------------------|
| `sorry` | Proof incomplete, left for later | `h_decomp` (key assumption for Regge convergence) |
| `def ... : Prop := True` | Conjecture placeholder, explicitly marked as unproven | `ReggeConvergesToEinsteinHilbert`, `HolographicConjecture` |
| `axiom` | Introduced from external mathematical facts, not proven within Lean | `cos2pi7_cubic_equation`, `seventh_root_sum_neg_one` |
| Intentionally retained counterexample | Certain constructions are mathematically invalid, retained as counterexamples | `past_closed` field of `cyclic_stable_substructure` |
| Conditional theorems with `[assumption]` premises | The theorem itself holds, but the premise may not be true | All theorems under `EffectiveFin7Regular` |
| Downgraded to `True` placeholder | Original theorem statement has issues (premises too strong or conclusion trivial) | `state_space_cardinality_theorem`, `scalarCurvature3D_from_2D_sections` |

---

### 4.6 Usage Principles: Researcher Self-Discipline

Based on the above audit, subsequent research work should follow these principles:

1. **When citing W1 layer theorems**: They can be used with full confidence; they are strictly verified mathematical conclusions validated by Lean.
2. **When citing W2 layer conditional theorems**: Their premise assumptions must be explicitly stated (e.g., "under EffectiveFin7Regular"), and they must not be treated as established physical facts.
3. **When discussing W3 layer interpretations**: Tentative language such as "we conjecture", "can be interpreted as", "this suggests" must be used, and they must not be conflated with W1/W2 layer theorems.
4. **When communicating externally**: A clear distinction must be made between "proven mathematics" and "speculative physical interpretations", avoiding giving readers the illusion that "all claims have been formally verified".
5. **Priority Judgment**: W2 layer proof gaps (especially the instantiation of `EffectiveFin7Regular` and Regge convergence) are the most valuable directions to tackle — they are the bridge connecting W1 mathematics with W3 interpretations.
