/-
================================================================================
CSQIT-LayerTower · Tower
模块: CSQIT_LayerTower.Tower
分层 AxiomC 塔的载体骨架、余极限构造与逐层因果判据

纪律：
  · 零新增 `axiom`、零 `sorry`（含 `admit` / `sorryAx` 变体）；
  · 不改动既有 474 条声明的陈述与证明；
  · 不触碰 CSQIT_W1 / CSQIT_Enhanced。

档位约定（全文 docstring 标出）：
  · B 档：需要新增定义，但不需要新增公设；定理机检通过。
  · A 档：不需要新增定义，直接由既有字段/既有定理推出。
  · C 档：需要新增公设，永不计作定理。

本文件只做结构层：塔的形状、层与顶的模型、余极限泛性质、
逐层 input 压平、逐层因果序判据。具体见证模型与塔顶的地位判定见 Top.lean。
================================================================================ -/

import CSQIT_W1.CoreCollapse
import CSQIT_V1Bridge.AmplitudeRigidity
import CSQIT_V1Bridge.OrderUniqueness

namespace CSQIT_LayerTower

open CSQIT_W1.Foundation

/-! ============================================================================
   §1. 塔的形状（B 档：新增结构定义，零公设）
   ============================================================================

   形状定为 `L₀ ⊆ L₁ ⊆ … ⊆ L_∞`：

   · 索引只要求 `LinearOrder`，**刻意不要求有最大元**；
     这样 `L_∞` 不是任何一个有限层，也不需要 `WithTop` 之类的额外构造。
   · 层间一律是**嵌入**：`Lᵢ ↪ L_∞`（结构保持单射），不是投影。
     理由见 DESIGN.md §2：投影需要统一的保结构满射，而
     G1（`no_uniform_compatible_order`）与 G23（`no_surjective_self_pi`）
     各自封死一侧。
   · 余极限在 `Set` 里取载体（有向并），再在 `Type` 里重建模型结构。 -/

/-- 分层塔数据：一条单调递增、逐层对 `compose` 封闭、逐层非空的载体族。 -/
structure RuleTower (M C : Type*) [A : AxiomA M C] (ι : Type*) [LinearOrder ι] where
  /-- 第 `i` 层的载体（`C` 的子集） -/
  carrier : ι → Set C
  /-- 层间单调：`i ≤ j ⇒ Lᵢ ⊆ Lⱼ` -/
  monotone_carrier : Monotone carrier
  /-- 每层对 `compose` 封闭（层内组合不出层） -/
  closed_compose : ∀ i : ι, ∀ a : C, a ∈ carrier i → ∀ b : C, b ∈ carrier i →
    A.compose a b ∈ carrier i
  /-- 每层非空（“每层有规则”） -/
  nonempty_layer : ∀ i : ι, (carrier i).Nonempty

variable {M C : Type*} [A : AxiomA M C]
variable {ι : Type*} [LinearOrder ι]

/-! ============================================================================
   §2. 顶层：Set 级余极限（B 档）
   ============================================================================ -/

/-- 塔顶载体：所有层的并。`ι` 无最大元时依然有定义。 -/
def top (T : RuleTower M C ι) : Set C := ⋃ i, T.carrier i

/-- 第 `i` 层作为独立载体的类型。 -/
def layer (T : RuleTower M C ι) (i : ι) : Type _ := {x : C // x ∈ T.carrier i}

/-- 塔顶作为独立载体的类型。 -/
def topType (T : RuleTower M C ι) : Type _ := {x : C // x ∈ top T}

theorem mem_top_iff {T : RuleTower M C ι} {x : C} :
    x ∈ top T ↔ ∃ i : ι, x ∈ T.carrier i := Set.mem_iUnion

/-- 顶层对 `compose` 封闭。关键点：两个元素可以来自不同层，
    用线性序的 `max` 把它们推到同一层。 -/
theorem top_closed (T : RuleTower M C ι) {a b : C} (ha : a ∈ top T) (hb : b ∈ top T) :
    A.compose a b ∈ top T := by
  simp only [top, Set.mem_iUnion] at ha hb ⊢
  obtain ⟨i, hi⟩ := ha
  obtain ⟨j, hj⟩ := hb
  exact ⟨max i j,
    T.closed_compose (max i j) a (T.monotone_carrier (le_max_left i j) hi)
      b (T.monotone_carrier (le_max_right i j) hj)⟩

/-! ============================================================================
   §3. 每层是完整模型：AxiomA / AxiomC 的限制继承（B 档）
   ============================================================================ -/

/-- 第 `i` 层上的 `AxiomA`：全部字段取环境模型在子集上的限制。 -/
instance layerAxiomA (T : RuleTower M C ι) (i : ι) : AxiomA M (layer T i) where
  input := fun x => A.input x.1
  output := fun x => A.output x.1
  input_nodup := fun x => A.input_nodup x.1
  compose := fun x y => ⟨A.compose x.1 y.1, T.closed_compose i x.1 x.2 y.1 y.2⟩
  compose_input := fun x y => A.compose_input x.1 y.1
  compose_output := fun x y => A.compose_output x.1 y.1
  compose_assoc := fun x y z => Subtype.ext (A.compose_assoc x.1 y.1 z.1)

/-- 塔顶上的 `AxiomA`。 -/
instance topAxiomA (T : RuleTower M C ι) : AxiomA M (topType T) where
  input := fun x => A.input x.1
  output := fun x => A.output x.1
  input_nodup := fun x => A.input_nodup x.1
  compose := fun x y => ⟨A.compose x.1 y.1, top_closed T x.2 y.2⟩
  compose_input := fun x y => A.compose_input x.1 y.1
  compose_output := fun x y => A.compose_output x.1 y.1
  compose_assoc := fun x y z => Subtype.ext (A.compose_assoc x.1 y.1 z.1)

/-- 第 `i` 层上的 `AxiomC`：振幅取限制，单射性由环境单射性继承。 -/
instance layerAxiomC (T : RuleTower M C ι) (i : ι) [Cx : AxiomC M C] :
    AxiomC M (layer T i) where
  amplitude := fun x => Cx.amplitude x.1
  norm_one := fun x => Cx.norm_one x.1
  comp_rule := fun x y => Cx.comp_rule x.1 y.1
  amplitude_injective := fun _ _ h => Subtype.ext (Cx.amplitude_injective h)

/-- 塔顶上的 `AxiomC`。 -/
instance topAxiomC (T : RuleTower M C ι) [Cx : AxiomC M C] :
    AxiomC M (topType T) where
  amplitude := fun x => Cx.amplitude x.1
  norm_one := fun x => Cx.norm_one x.1
  comp_rule := fun x y => Cx.comp_rule x.1 y.1
  amplitude_injective := fun _ _ h => Subtype.ext (Cx.amplitude_injective h)

/-- **B 档**：塔顶确实是 `AxiomA + AxiomC` 模型（不是原始类型）。
    证明了什么：逐层/顶层模型的**存在性**是构造性的，不需要额外公设。
    不证明什么：顶是否承载因果序、唯一序、自生成、引力（见 Top.lean）。 -/
theorem top_model_exists (T : RuleTower M C ι) [Cx : AxiomC M C] :
    Nonempty (AxiomA M (topType T)) ∧ Nonempty (AxiomC M (topType T)) :=
  ⟨⟨topAxiomA T⟩, ⟨topAxiomC T⟩⟩

/-! ============================================================================
   §4. 余极限泛性质与嵌入（B 档）
   ============================================================================ -/

/-- **Set 级余极限泛性质**：`top` 是包含全部层的最小集合。
    这条把“塔顶 = 余极限”变成可机检的命题（而不是叙事）。 -/
theorem top_is_colimit (T : RuleTower M C ι) (S : Set C) :
    top T ⊆ S ↔ ∀ i : ι, T.carrier i ⊆ S := by
  constructor
  · intro h i a ha
    exact h (by
      simp only [top, Set.mem_iUnion]
      exact ⟨i, ha⟩)
  · intro h a ha
    simp only [top, Set.mem_iUnion] at ha
    obtain ⟨i, hi⟩ := ha
    exact h i hi

/-- 层到顶的嵌入（结构保持单射）。 -/
def layerToTop (T : RuleTower M C ι) (i : ι) : layer T i → topType T :=
  fun x => ⟨x.1, by
    simp only [top, Set.mem_iUnion]
    exact ⟨i, x.2⟩⟩

theorem layerToTop_injective (T : RuleTower M C ι) (i : ι) :
    Function.Injective (layerToTop T i) := by
  intro x y h
  have h' : x.1 = y.1 := congrArg (fun z : topType T => z.1) h
  exact Subtype.ext h'

/-- 嵌入保持 `compose`（层间是嵌入而非投影的直接证据）。 -/
theorem layerToTop_compose (T : RuleTower M C ι) (i : ι) (x y : layer T i) :
    layerToTop T i ((layerAxiomA T i).compose x y)
      = (topAxiomA T).compose (layerToTop T i x) (layerToTop T i y) :=
  Subtype.ext rfl

/-- **B 档**：层内因果可达关系随嵌入**单向上行**（层序 ⊆ 顶序）。
    证明了什么：任何在层内成立的 `x ≺ x∘γ`，在塔顶也成立。
    不证明什么：反向不成立——顶可以用更高层的见证元素建立层内不存在的边，
    因此“顶序 = 各层序的并”不能由这条定理推出（见 DESIGN.md §4）。 -/
theorem layerToTop_reach (T : RuleTower M C ι) (i : ι) {x y : layer T i}
    (h : CSQIT_V1Bridge.oneStepReach (layerAxiomA T i) x y) :
    CSQIT_V1Bridge.oneStepReach (topAxiomA T) (layerToTop T i x) (layerToTop T i y) := by
  unfold CSQIT_V1Bridge.oneStepReach at h ⊢
  obtain ⟨γ, hγ, hne⟩ := h
  refine ⟨layerToTop T i γ, ?_, ?_⟩
  · apply Subtype.ext
    exact congrArg (fun z : layer T i => z.1) hγ
  · intro hxy
    exact hne (layerToTop_injective T i hxy)

/-! ============================================================================
   §5. 逐层字段行为：input 被压平（A 档）
   ============================================================================ -/

/-- **A 档（复用 core_collapse）**：每一层的 `input` 恒为空。
    证明了什么：依赖层不能沿塔分层——`input` 在每一层都是 `[]`。
    不证明什么：`output` / `compose` / 振幅的分层能力（它们仍可分层）。 -/
theorem layer_input_empty (T : RuleTower M C ι) (i : ι) (x : layer T i) :
    (layerAxiomA T i).input x = [] :=
  CSQIT_W1.CoreCollapse.input_must_be_empty (A := layerAxiomA T i) x

/-- **A 档（复用 core_collapse）**：塔顶的 `input` 恒为空。 -/
theorem top_input_empty (T : RuleTower M C ι) (x : topType T) :
    (topAxiomA T).input x = [] :=
  CSQIT_W1.CoreCollapse.input_must_be_empty (A := topAxiomA T) x

/-! ============================================================================
   §6. 逐层因果序判据（A 档，G39b 的分层形式）
   ============================================================================

   G1 说“五字段不能统一导出因果序”。但塔住在 `AxiomC` 世界里，
   那里有一条纯振幅判据（G39b）：因果层存在 ⟺ `1 ∉ range(amplitude)`。
   把它限制到每层，就得到“哪一层能承载因果序”的精确条件。
   这就是塔层需要因果序时**绕开 G1 的唯一条件**：不是靠新公设，
   而是靠该层振幅值域避开 1。 -/

/-- 与 `compose` 相容的严格偏序（与 G1/G34 使用的形状逐字一致）。 -/
def Compatible {M C : Type*} (Ax : AxiomA M C) (r : C → C → Prop) : Prop :=
  (∀ x : C, ¬ r x x) ∧
  (∀ x y z : C, r x y → r y z → r x z) ∧
  (∀ α β : C, r α (Ax.compose α β))

/-- **A 档（G39b 分层版）**：第 `i` 层有相容严格偏序 ⟺ 该层不含振幅 1 的元素。 -/
theorem layer_has_order_iff (T : RuleTower M C ι) (i : ι) [Cx : AxiomC M C] :
    (∃ r : layer T i → layer T i → Prop, Compatible (layerAxiomA T i) r) ↔
    (∀ x : layer T i, (layerAxiomC T i).amplitude x ≠ 1) :=
  CSQIT_V1Bridge.exists_compatible_order_iff_amplitude_ne_one
    (A := layerAxiomA T i) (Cx := layerAxiomC T i)

/-- **A 档**：塔顶有相容严格偏序 ⟺ 顶不含振幅 1 的元素。 -/
theorem top_has_order_iff (T : RuleTower M C ι) [Cx : AxiomC M C] :
    (∃ r : topType T → topType T → Prop, Compatible (topAxiomA T) r) ↔
    (∀ x : topType T, (topAxiomC T).amplitude x ≠ 1) :=
  CSQIT_V1Bridge.exists_compatible_order_iff_amplitude_ne_one
    (A := topAxiomA T) (Cx := topAxiomC T)

/-- **A 档**：因果序能力沿塔**单调衰减**——层越高，越可能失去因果序。
    因此“塔顶自动继承因果序”为假：条件只能逐层检查。 -/
theorem layer_no_one_mono (T : RuleTower M C ι) [AxiomC M C] {i j : ι}
    (hij : i ≤ j) (h : ∀ x : layer T j, (layerAxiomC T j).amplitude x ≠ 1) :
    ∀ x : layer T i, (layerAxiomC T i).amplitude x ≠ 1 := by
  intro x
  exact h ⟨x.1, T.monotone_carrier hij x.2⟩

/-- **A 档**：上一条的序版本（层 `j` 有序 ⇒ 所有下层有序）。 -/
theorem layer_has_order_mono (T : RuleTower M C ι) [Cx : AxiomC M C] {i j : ι}
    (hij : i ≤ j)
    (h : ∃ r : layer T j → layer T j → Prop, Compatible (layerAxiomA T j) r) :
    ∃ r : layer T i → layer T i → Prop, Compatible (layerAxiomA T i) r :=
  (layer_has_order_iff T i).mpr
    (layer_no_one_mono (i := i) (j := j) T hij ((layer_has_order_iff T j).mp h))

/-- **A 档**：塔顶的因果序恰是所有层因果序的**合取**，不是层序的并。 -/
theorem top_has_order_iff_all_layers (T : RuleTower M C ι) [Cx : AxiomC M C] :
    (∃ r : topType T → topType T → Prop, Compatible (topAxiomA T) r) ↔
    ∀ i : ι, ∃ r : layer T i → layer T i → Prop, Compatible (layerAxiomA T i) r := by
  rw [top_has_order_iff]
  constructor
  · intro h i
    exact (layer_has_order_iff T i).mpr (fun x => h ⟨x.1, by
      simp only [top, Set.mem_iUnion]
      exact ⟨i, x.2⟩⟩)
  · intro h x
    obtain ⟨i, hi⟩ := by
      simpa only [top, Set.mem_iUnion] using x.2
    exact (layer_has_order_iff T i).mp (h i) ⟨x.1, hi⟩

/-- **A 档（否定式）**：只要塔顶含一个振幅 1 的元素，顶就没有相容严格偏序。 -/
theorem top_no_order_of_amp_one (T : RuleTower M C ι) [Cx : AxiomC M C]
    {x : C} (hx : x ∈ top T) (h1 : Cx.amplitude x = 1) :
    ¬ ∃ r : topType T → topType T → Prop, Compatible (topAxiomA T) r := by
  rw [top_has_order_iff]
  intro h
  exact h ⟨x, hx⟩ h1

end CSQIT_LayerTower
