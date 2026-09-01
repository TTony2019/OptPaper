import Mathlib

/-!
# Analysis ExtendedRealFunctions

Domains, epigraphs, minimizing sequences, pointwise sums, and effective domains of extended-real
functions.
-/

open EReal
open Set
open Filter

/-! Source item: Alvarez 2002 Definition (indicator function) -/

/-- The indicator function `Ψ_K` of a set `K`, with values in the extended reals. -/
noncomputable def indicatorFunction {H : Type*} (K : Set H) (x : H) : EReal := by
  classical
  exact if x ∈ K then 0 else ⊤

/-- The indicator function unfolds to the defining `if-then-else`. -/
@[simp]
theorem indicatorFunction_apply {H : Type*} (K : Set H) (x : H) [Decidable (x ∈ K)] :
    indicatorFunction K x = if x ∈ K then (0 : EReal) else ⊤ := by
  by_cases hx : x ∈ K <;> simp [indicatorFunction, hx]

/-- Bridge: the `Set.indicator Cᶜ (fun _ ↦ ⊤)` form equals the indicator of `C`. -/
@[simp]
theorem indicatorFunction_eq_setIndicator_compl_top (C : Set H) (x : H) :
    Set.indicator Cᶜ (fun _ : H ↦ (⊤ : EReal)) x = indicatorFunction C x := by
  by_cases hx : x ∈ C <;> simp [Set.indicator, indicatorFunction, hx]

/-! Source item: Chap01/Definition_1_4 -/
universe u

namespace ERealFunction

variable {X : Type u}

/-- The domain of an extended-real-valued function is the set of points where the value is
strictly less than `+∞`. -/
def dom (f : X → EReal) : Set X := f ⁻¹' Set.Iio ⊤

/-- A point belongs to the domain exactly when the function value is finite above. -/
@[simp]
theorem mem_dom_iff (f : X → EReal) (x : X) :
  x ∈ dom f ↔ f x < ⊤ := Iff.rfl

/-- The graph of an extended-real-valued function is the set of pairs `(x, ξ)` with real ordinate
`ξ` equal to the function value at `x`. -/
def graph (f : X → EReal) : Set (X × ℝ) := { p | f p.1 = (p.2 : EReal) }

/-- A real pair belongs to the graph exactly when its second coordinate equals the function
value. -/
@[simp]
theorem mem_graph_iff (f : X → EReal) (x : X) (ξ : ℝ) :
  (x, ξ) ∈ graph f ↔ f x = (ξ : EReal) := Iff.rfl

/-- The epigraph of an extended-real-valued function is the set of pairs `(x, ξ)` with real
ordinate `ξ` lying above the function value at `x`. -/
def epigraph (f : X → EReal) : Set (X × ℝ) := { p | f p.1 ≤ (p.2 : EReal) }

/-- A real pair belongs to the epigraph exactly when its second coordinate majorizes the function
value. -/
@[simp]
theorem mem_epigraph_iff (f : X → EReal) (x : X) (ξ : ℝ) :
    (x, ξ) ∈ epigraph f ↔ f x ≤ (ξ : EReal) :=
  Iff.rfl

/-- The lower level set at height `ξ` is the set of points where the function value is at most
`ξ`. -/
def lowerLevelSet (f : X → EReal) (ξ : ℝ) : Set X := f ⁻¹' Set.Iic (ξ : EReal)

/-- A point belongs to the lower level set at height `ξ` exactly when the function value is at most
`ξ`. -/
@[simp]
theorem mem_lowerLevelSet_iff (f : X → EReal) (ξ : ℝ) (x : X) :
    x ∈ lowerLevelSet f ξ ↔ f x ≤ (ξ : EReal) :=
  Iff.rfl

/-- The strict lower level set at height `ξ` is the set of points where the function value is
strictly less than `ξ`. -/
def strictLowerLevelSet (f : X → EReal) (ξ : ℝ) : Set X := f ⁻¹' Set.Iio (ξ : EReal)

/-- A point belongs to the strict lower level set at height `ξ` exactly when the function value is
strictly less than `ξ`. -/
@[simp]
theorem mem_strictLowerLevelSet_iff (f : X → EReal) (ξ : ℝ) (x : X) :
    x ∈ strictLowerLevelSet f ξ ↔ f x < (ξ : EReal) :=
  Iff.rfl

/-- Definition 1.4: an extended-real-valued function is proper when it never attains `-∞` and its
domain is nonempty. -/
def IsProper (f : X → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ (dom f).Nonempty

/-- A function is proper exactly when it never takes the value `-∞` and its domain is nonempty. -/
@[simp]
theorem isProper_iff (f : X → EReal) :
    IsProper f ↔ (∀ x, f x ≠ ⊥) ∧ (dom f).Nonempty :=
  Iff.rfl

/-- A function is proper exactly when `-∞` is not in its range and its domain is nonempty. -/
theorem isProper_iff_bot_notMem_range (f : X → EReal) :
    IsProper f ↔ ⊥ ∉ Set.range f ∧ (dom f).Nonempty := by
  simp [IsProper]

/-- A real-valued function is proper when coerced to the extended reals, provided the domain is
nonempty. -/
theorem isProper_coe_real [Zero X] (f : X → ℝ) : IsProper fun x => (f x : EReal) := by
  constructor
  · intro x
    exact EReal.coe_ne_bot (f x)
  · refine ⟨0, ?_⟩
    exact (mem_dom_iff _ 0).2 (EReal.coe_lt_top (f 0))

end ERealFunction

/-! Source item: Chap01/Definition_1_7 -/


namespace ERealFunction

variable {X : Type u}

/-- Definition 1.7 (1): the infimum of an extended-real-valued function over a set is the infimum
of its image on that set, namely `sInf (f '' C)`. -/
theorem isGLB_sInf_image (f : X → EReal) (C : Set X) :
    IsGLB (f '' C) (sInf (f '' C)) :=
  isGLB_sInf (f '' C)

/-- Definition 1.7 (3): a minimizer of `f` on `C` realizes the infimum of `f` on `C`. -/
theorem eq_sInf_image_of_isMinOn {f : X → EReal} {C : Set X} {x : X}
    (hx : x ∈ C) (hmin : IsMinOn f C x) :
    f x = sInf (f '' C) := by
  have hglb : IsGLB (f '' C) (f x) := by
    simpa only [mem_image] using hmin.isGLB hx
  exact hglb.unique (isGLB_sInf_image f C)

/-- Definition 1.7 (2): a function achieves its infimum over `C` exactly when some point of `C`
is a minimizer, equivalently when some point of `C` evaluates to `sInf (f '' C)`. -/
theorem exists_isMinOn_iff_exists_eq_sInf_image (f : X → EReal) (C : Set X) :
    (∃ x ∈ C, IsMinOn f C x) ↔ ∃ x ∈ C, f x = sInf (f '' C) := by
  constructor
  · rintro ⟨x, hxC, hmin⟩
    exact ⟨x, hxC, eq_sInf_image_of_isMinOn hxC hmin⟩
  · rintro ⟨x, hxC, hx⟩
    refine ⟨x, hxC, ?_⟩
    rw [isMinOn_iff]
    intro y hyC
    have hsInf_le : sInf (f '' C) ≤ f y := by
      exact (isGLB_sInf_image f C).1 (mem_image_of_mem f hyC)
    simpa [hx] using hsInf_le

/-- Definition 1.7 (4): the supremum of an extended-real-valued function over a set is the
supremum of its image on that set, namely `sSup (f '' C)`. -/
theorem isLUB_sSup_image (f : X → EReal) (C : Set X) :
    IsLUB (f '' C) (sSup (f '' C)) :=
  isLUB_sSup (f '' C)

/-- Definition 1.7 (6): a maximizer of `f` on `C` realizes the supremum of `f` on `C`. -/
theorem eq_sSup_image_of_isMaxOn {f : X → EReal} {C : Set X} {x : X}
    (hx : x ∈ C) (hmax : IsMaxOn f C x) :
    f x = sSup (f '' C) := by
  have hlub : IsLUB (f '' C) (f x) := by
    simpa only [mem_image] using hmax.isLUB hx
  exact hlub.unique (isLUB_sSup_image f C)

/-- Definition 1.7 (5): a function achieves its supremum over `C` exactly when some point of `C`
is a maximizer, equivalently when some point of `C` evaluates to `sSup (f '' C)`. -/
theorem exists_isMaxOn_iff_exists_eq_sSup_image (f : X → EReal) (C : Set X) :
    (∃ x ∈ C, IsMaxOn f C x) ↔ ∃ x ∈ C, f x = sSup (f '' C) := by
  constructor
  · rintro ⟨x, hxC, hmax⟩
    exact ⟨x, hxC, eq_sSup_image_of_isMaxOn hxC hmax⟩
  · rintro ⟨x, hxC, hx⟩
    refine ⟨x, hxC, ?_⟩
    rw [isMaxOn_iff]
    intro y hyC
    have hy_le : f y ≤ sSup (f '' C) := by
      exact (isLUB_sSup_image f C).1 (mem_image_of_mem f hyC)
    simpa [hx] using hy_le

end ERealFunction

/-! Source item: Chap01/Definition_1_8 -/


namespace ERealFunction

variable {X : Type u}

/-- Definition 1.8: a sequence in the domain of an extended-real-valued function is minimizing
when its function values converge to the infimum of the image of the function. -/
def IsMinimizingSequence (f : X → EReal) (x : ℕ → X) : Prop :=
  (∀ n : ℕ, x n ∈ dom f) ∧ Tendsto (f ∘ x) atTop (nhds (sInf (Set.range f)))

/-- A minimizing sequence takes values in the domain of the function termwise. -/
theorem IsMinimizingSequence.mem_dom {f : X → EReal} {x : ℕ → X}
    (hx : IsMinimizingSequence f x) (n : ℕ) :
    x n ∈ dom f :=
  hx.1 n

/-- Helper for Definition 1.8: a minimizing sequence has function values strictly below `+∞`
termwise. -/
theorem IsMinimizingSequence.lt_top {f : X → EReal} {x : ℕ → X}
    (hx : IsMinimizingSequence f x) (n : ℕ) :
    f (x n) < ⊤ := by
  simpa [mem_dom_iff] using hx.mem_dom n

/-- A minimizing sequence has function values converging to the infimum of the image of `f`. -/
theorem IsMinimizingSequence.tendsto {f : X → EReal} {x : ℕ → X}
    (hx : IsMinimizingSequence f x) :
    Tendsto (f ∘ x) atTop (nhds (sInf (Set.range f))) :=
  hx.2

/-- A sequence is minimizing exactly when all of its function values are strictly below `+∞` and
those values converge to the infimum of the image of `f`. -/
theorem isMinimizingSequence_iff_lt_top (f : X → EReal) (x : ℕ → X) :
    IsMinimizingSequence f x ↔
      (∀ n : ℕ, f (x n) < ⊤) ∧ Tendsto (f ∘ x) atTop (nhds (sInf (Set.range f))) := by
  simp [IsMinimizingSequence, mem_dom_iff]

end ERealFunction

/-! Source item: Chap01/Lemma_1_6 -/

universe v

namespace ERealFunction

-- Proof sketch: extensionality on pairs `(x, ξ)` reduces the claim to the order fact
-- `iSup_le_iff`, which says `⨆ i, f i x ≤ ξ` iff `∀ i, f i x ≤ ξ`.
/-- Lemma 1.6 (1): the epigraph of the pointwise supremum of a family of extended-real-valued
functions is the intersection of the epigraphs of the family members. -/
theorem epigraph_iSup {X : Type u} {I : Type v} (f : I → X → EReal) :
    epigraph (⨆ i, f i) = ⋂ i, epigraph (f i) := by
  ext p
  rcases p with ⟨x, ξ⟩
  -- Membership on both sides is an upper-bound condition at `(x, ξ)`.
  simp [iSup_le_iff]

-- Proof sketch: extensionality on `(x, ξ)` reduces the statement to the finite complete-lattice
-- identity `iInf_le_iff`, which under `[Finite I]` rewrites `⨅ i, f i x ≤ ξ` as
-- `∃ i, f i x ≤ ξ`.
/-- Lemma 1.6 (2): if the index type is finite, then the epigraph of the pointwise minimum is the
union of the epigraphs of the family members. -/
theorem epigraph_iInf_of_finite {X : Type u} {I : Type v} [Finite I] (f : I → X → EReal) :
    epigraph (⨅ i, f i) = ⋃ i, epigraph (f i) := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  have hinf (x : X) (ξ : ℝ) :
      Finset.univ.inf (fun i : I ↦ f i x) ≤ (ξ : EReal) ↔
        ∃ i, f i x ≤ (ξ : EReal) := by
    have h :
        Finset.univ.inf (fun i : I ↦ f i x) ≤ (ξ : EReal) ↔
          ∃ i, i ∈ (Finset.univ : Finset I) ∧ f i x ≤ (ξ : EReal) :=
      Finset.inf_le_iff (EReal.coe_lt_top ξ)
    simp only [Finset.mem_univ, true_and] at h
    exact h
  ext p
  rcases p with ⟨x, ξ⟩
  constructor
  · intro hp
    rw [mem_epigraph_iff] at hp
    have hpx : (⨅ i, f i x) ≤ (ξ : EReal) := by
      simpa using hp
    rw [← Finset.inf_univ_eq_iInf (fun i : I ↦ f i x), hinf] at hpx
    rcases hpx with ⟨i, hi⟩
    exact Set.mem_iUnion.2 ⟨i, by simpa [mem_epigraph_iff] using hi⟩
  · intro hp
    rcases Set.mem_iUnion.1 hp with ⟨i, hi⟩
    rw [mem_epigraph_iff] at hi
    rw [mem_epigraph_iff]
    have hpx : (⨅ i, f i x) ≤ (ξ : EReal) := by
      rw [← Finset.inf_univ_eq_iInf (fun i : I ↦ f i x), hinf]
      exact ⟨i, hi⟩
    simpa using hpx

end ERealFunction

/-! Source item: Chap01/Lemma_1_24 -/

namespace ERealFunction

variable {X : Type u}

private lemma epigraph_eq_preimage_erealEpigraph (f : X → EReal) :
    epigraph f =
      (fun p : X × ℝ ↦ (p.1, (p.2 : EReal))) ⁻¹' {q : X × EReal | f q.1 ≤ q.2} := by
  rfl

private lemma lowerLevelSet_eq_preimage_epigraph (f : X → EReal) (ξ : ℝ) :
    lowerLevelSet f ξ = (fun x : X ↦ (x, ξ)) ⁻¹' epigraph f := by
  rfl

private lemma preimage_Ioi_eq_iUnion_compl_lowerLevelSet_rat (f : X → EReal) (α : EReal) :
    f ⁻¹' Set.Ioi α =
      ⋃ q : {q : ℚ // α < (((q : ℚ) : ℝ) : EReal)}, (lowerLevelSet f ((q : ℚ) : ℝ))ᶜ := by
  ext x
  constructor
  · intro hx
    rcases EReal.exists_rat_btwn_of_lt hx with ⟨q, hαq, hqf⟩
    refine Set.mem_iUnion.2 ⟨⟨q, hαq⟩, ?_⟩
    simpa [lowerLevelSet, Set.mem_compl, Set.mem_preimage, not_le] using hqf
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨q, hxq⟩
    have hαq : α < (((q : ℚ) : ℝ) : EReal) := q.2
    have hqf : ((((q : ℚ) : ℝ) : EReal) < f x) := by
      simpa [lowerLevelSet, Set.mem_compl, Set.mem_preimage, not_le] using hxq
    exact hαq.trans hqf

variable [TopologicalSpace X]

/-- Lemma 1.24: an extended-real-valued function on a topological space is lower semicontinuous if
and only if each of its real lower level sets is closed. -/
theorem lowerSemicontinuous_iff_isClosed_lowerLevelSet (f : X → EReal) :
    LowerSemicontinuous f ↔ ∀ ξ : ℝ, IsClosed (lowerLevelSet f ξ) := by
  constructor
  · intro hf ξ
    simpa [lowerLevelSet] using hf.isClosed_preimage ((ξ : ℝ) : EReal)
  · intro hLevel
    rw [lowerSemicontinuous_iff_isOpen_preimage]
    intro α
    rw [preimage_Ioi_eq_iUnion_compl_lowerLevelSet_rat]
    exact isOpen_iUnion fun q ↦ (hLevel ((q : ℚ) : ℝ)).isOpen_compl

/-- Lemma 1.24: an extended-real-valued function on a topological space is lower semicontinuous if
and only if its real-height epigraph is closed. -/
theorem lowerSemicontinuous_iff_isClosed_epigraph (f : X → EReal) :
    LowerSemicontinuous f ↔ IsClosed (epigraph f) := by
  constructor
  · intro hf
    rw [epigraph_eq_preimage_erealEpigraph]
    exact hf.isClosed_epigraph.preimage
      (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))
  · intro hEpi
    have hLevel : ∀ ξ : ℝ, IsClosed (lowerLevelSet f ξ) := by
      intro ξ
      rw [lowerLevelSet_eq_preimage_epigraph]
      exact hEpi.preimage (Continuous.prodMk continuous_id continuous_const)
    exact (lowerSemicontinuous_iff_isClosed_lowerLevelSet f).2 hLevel

/-- Textbook presentation of Lemma 1.24: lower semicontinuity, closedness of the real-height
epigraph, and closedness of all real lower level sets are equivalent assertions. -/
theorem lowerSemicontinuous_real_epigraph_closed_lowerLevelSet_closed_tfae (f : X → EReal) :
    List.TFAE [LowerSemicontinuous f, IsClosed (epigraph f),
      ∀ ξ : ℝ, IsClosed (lowerLevelSet f ξ)] := by
  tfae_have 1 → 2 := fun hf ↦
    (lowerSemicontinuous_iff_isClosed_epigraph f).1 hf
  tfae_have 2 → 3 := fun hEpi ↦
    (lowerSemicontinuous_iff_isClosed_lowerLevelSet f).1
      ((lowerSemicontinuous_iff_isClosed_epigraph f).2 hEpi)
  tfae_have 3 → 1 := fun hLevel ↦
    (lowerSemicontinuous_iff_isClosed_lowerLevelSet f).2 hLevel
  tfae_finish

end ERealFunction

/-! Source item: Chap01/Text_1_0_31 -/

namespace ERealFunction

variable {X : Type u}

/-- Text 1.0.31: the effective domain of an extended-real-valued function is the set of points
at which the function takes a finite value. Equivalently, it is the preimage of the open interval
`Ioo ⊥ ⊤`, i.e. the points where the value is neither `+∞` nor `-∞`. -/
def effectiveDom (f : X → EReal) : Set X :=
  f ⁻¹' Set.Ioo (⊥ : EReal) ⊤

/-- A point lies in the effective domain exactly when the function value there is finite, i.e. it
is neither `+∞` nor `-∞`. -/
@[simp] theorem mem_effectiveDom_iff (f : X → EReal) (x : X) :
    x ∈ effectiveDom f ↔ f x ≠ ⊤ ∧ f x ≠ ⊥ := by
  rw [effectiveDom, Set.mem_preimage, Set.mem_Ioo, bot_lt_iff_ne_bot, lt_top_iff_ne_top]
  constructor
  · intro hx
    exact ⟨hx.2, hx.1⟩
  · intro hx
    exact ⟨hx.2, hx.1⟩

/-- A point lies in the effective domain exactly when the function value there comes from a real
number via the canonical coercion `ℝ → EReal`. -/
theorem mem_effectiveDom_iff_exists_real (f : X → EReal) (x : X) :
    x ∈ effectiveDom f ↔ ∃ r : ℝ, f x = (r : EReal) := by
  constructor
  · intro hx
    rcases (mem_effectiveDom_iff f x).1 hx with ⟨h_top, h_bot⟩
    exact ⟨(f x).toReal, (EReal.coe_toReal h_top h_bot).symm⟩
  · rintro ⟨r, hr⟩
    simp [mem_effectiveDom_iff, hr]

/-- The effective domain is the part of the ordinary domain where the function also avoids
`-∞`. -/
theorem effectiveDom_eq_dom_inter_neBot (f : X → EReal) :
    effectiveDom f = dom f ∩ {x | f x ≠ ⊥} := by
  ext x
  rw [Set.mem_inter_iff, Set.mem_setOf_eq, mem_effectiveDom_iff, mem_dom_iff, lt_top_iff_ne_top]

end ERealFunction

/-! Source item: Chap01/Text_1_0_32 -/

noncomputable section

namespace EReal

variable {X : Type u}

/-- Text 1.0.32: addition on `EReal` with the textbook convention that the indeterminate sums
`+∞ + -∞` and `-∞ + +∞` are assigned the value `+∞`. -/
def sumWithTopBotAsTop : EReal → EReal → EReal
  | ⊤, ⊥ => ⊤
  | ⊥, ⊤ => ⊤
  | x, y => x + y

/-- Text 1.0.32: the textbook pointwise sum of two extended-real-valued functions is obtained by
applying the textbook extended-real addition convention pointwise. -/
abbrev pointwiseSum (f g : X → EReal) : X → EReal :=
  fun x ↦ sumWithTopBotAsTop (f x) (g x)

/-- Evaluating the textbook pointwise sum amounts to applying the textbook extended-real
addition convention at the chosen point. -/
@[simp] theorem pointwiseSum_apply (f g : X → EReal) (x : X) :
    pointwiseSum f g x = sumWithTopBotAsTop (f x) (g x) :=
  rfl

/-- The textbook addition convention is finite exactly when both inputs are finite real values. -/
theorem exists_real_eq_sumWithTopBotAsTop_iff {a b : EReal} :
    (∃ r : ℝ, sumWithTopBotAsTop a b = (r : EReal)) ↔
      (∃ s : ℝ, a = (s : EReal)) ∧ ∃ t : ℝ, b = (t : EReal) := by
  cases a <;> cases b
  case bot.bot =>
    change (∃ r : ℝ, (⊥ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (⊥ : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (⊥ : EReal) = (t : EReal)
    simp
  case bot.coe b =>
    change (∃ r : ℝ, (⊥ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (⊥ : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (b : EReal) = (t : EReal)
    simp
  case bot.top =>
    change (∃ r : ℝ, (⊤ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (⊥ : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (⊤ : EReal) = (t : EReal)
    simp
  case coe.bot a =>
    change (∃ r : ℝ, (⊥ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (a : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (⊥ : EReal) = (t : EReal)
    simp
  case coe.coe a b =>
    change (∃ r : ℝ, (a : EReal) + (b : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (a : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (b : EReal) = (t : EReal)
    constructor
    · intro _
      exact ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    · intro _
      refine ⟨a + b, ?_⟩
      exact (EReal.coe_add a b).symm
  case coe.top a =>
    change (∃ r : ℝ, (⊤ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (a : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (⊤ : EReal) = (t : EReal)
    simp
  case top.bot =>
    change (∃ r : ℝ, (⊤ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (⊤ : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (⊥ : EReal) = (t : EReal)
    simp
  case top.coe b =>
    change (∃ r : ℝ, (⊤ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (⊤ : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (b : EReal) = (t : EReal)
    simp
  case top.top =>
    change (∃ r : ℝ, (⊤ : EReal) = (r : EReal)) ↔
      (∃ s : ℝ, (⊤ : EReal) = (s : EReal)) ∧ ∃ t : ℝ, (⊤ : EReal) = (t : EReal)
    simp

end EReal

end

/-! Source item: Chap01/Text_1_0_33 -/


namespace ERealFunction

variable {X : Type u}

/-- A point belongs to the effective domain of the textbook pointwise sum exactly when it belongs
to the effective domains of both summands. -/
lemma mem_effectiveDom_pointwiseSum_iff (f g : X → EReal) (x : X) :
    x ∈ effectiveDom (pointwiseSum f g) ↔ x ∈ effectiveDom f ∧ x ∈ effectiveDom g := by
  rw [mem_effectiveDom_iff_exists_real, pointwiseSum_apply, exists_real_eq_sumWithTopBotAsTop_iff,
    mem_effectiveDom_iff_exists_real, mem_effectiveDom_iff_exists_real]

/-- Text 1.0.33: the effective domain of the textbook pointwise sum of two extended-real-valued
functions is the intersection of their effective domains. -/
theorem effectiveDom_pointwiseSum_eq_inter (f g : X → EReal) :
    effectiveDom (pointwiseSum f g) = effectiveDom f ∩ effectiveDom g := by
  ext x
  rw [Set.mem_inter_iff, mem_effectiveDom_pointwiseSum_iff]

end ERealFunction

/-! Source item: Chap01/Text_1_0_55 -/

namespace ERealFunction

variable {X : Type u} [TopologicalSpace X]

/-- Text 1.0.55: the points where an `EReal`-valued function takes a real value and is continuous
are exactly the points in its effective domain at which it is continuous. -/
theorem mem_effectiveDom_inter_continuousAt_iff_exists_real (f : X → EReal) (x : X) :
    x ∈ effectiveDom f ∩ {y | ContinuousAt f y} ↔
      (∃ r : ℝ, f x = (r : EReal)) ∧ ContinuousAt f x := by
  rw [Set.mem_inter_iff, Set.mem_setOf_eq, mem_effectiveDom_iff_exists_real]

end ERealFunction

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap08/Text_8_0_1 -/

namespace ERealFunction

/-- Multiplying a `]-∞,+∞]`-value by a positive real again yields a `]-∞,+∞]`-value. -/
theorem adjoint_mul_mem_Ioi_bot (ξ : ℝ) (hξ : 0 < ξ) (x : Set.Ioi (⊥ : EReal)) :
    (⊥ : EReal) < (ξ : EReal) * (x : EReal) := by
  rw [bot_lt_iff_ne_bot]
  exact (EReal.mul_ne_bot _ _).2
    ⟨Or.inl (EReal.coe_ne_bot ξ), Or.inr x.property.ne', Or.inl (EReal.coe_ne_top ξ),
      Or.inl (EReal.coe_nonneg.2 hξ.le)⟩

/-- The canonical positive-real parameter type `ℝ_{++}` used for scalar actions on
`]-∞,+∞]`-valued functions. -/
abbrev PosReal := {x : ℝ // 0 < x}

/-- The multiplicative unit of `ℝ_{++}`. -/
instance : One PosReal := ⟨⟨1, by positivity⟩⟩

/-- Any numeral at least `2` defines a canonical element of `ℝ_{++}`. -/
instance instOfNatPosReal (n : Nat) : OfNat PosReal (n + 2) :=
  ⟨⟨n + 2, by positivity⟩⟩

/-- Positive reals are closed under multiplication. -/
instance : Mul PosReal := ⟨fun a b ↦ ⟨(a : ℝ) * (b : ℝ), mul_pos a.2 b.2⟩⟩

@[simp] theorem posReal_coe_one : ((1 : PosReal) : ℝ) = 1 := by
  change ((⟨1, by positivity⟩ : PosReal) : ℝ) = 1
  rfl

@[simp] theorem posReal_coe_mul (a b : PosReal) : ((a * b : PosReal) : ℝ) = (a : ℝ) * (b : ℝ) :=
  rfl

instance : Monoid PosReal where
  mul_assoc a b c := by
    apply Subtype.ext
    simp [mul_assoc]
  one_mul a := by
    apply Subtype.ext
    change ((1 : ℝ) * (a : ℝ)) = (a : ℝ)
    simp
  mul_one a := by
    apply Subtype.ext
    change ((a : ℝ) * (1 : ℝ)) = (a : ℝ)
    simp

/-- The effective domain of an `]-∞,+∞]`-valued function. -/
def effectiveDomain (f : H → Set.Ioi (⊥ : EReal)) : Set H :=
  {x | (f x : EReal) < ⊤}

/-- Membership in the effective domain means that the function value is finite. -/
theorem mem_effectiveDomain_iff {f : H → Set.Ioi (⊥ : EReal)} {x : H} :
    x ∈ effectiveDomain f ↔ (f x : EReal) < ⊤ :=
  Iff.rfl

/-- The pointwise sum of two `]-∞,+∞]`-valued functions. -/
noncomputable def pointwiseAdd (f g : H → Set.Ioi (⊥ : EReal)) : H → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    ⟨(f x : EReal) + (g x : EReal),
      EReal.bot_lt_add_iff.2 ⟨(f x).property, (g x).property⟩⟩

/-- Coercing the pointwise sum back to `EReal` recovers ordinary pointwise addition. -/
@[simp] theorem pointwiseAdd_apply (f g : H → Set.Ioi (⊥ : EReal)) (x : H) :
    (pointwiseAdd f g x : EReal) = (f x : EReal) + (g x : EReal) := by
  rfl

/-- Positive reals act on `]-∞,+∞]` by multiplication. -/
noncomputable instance : SMul PosReal (Set.Ioi (⊥ : EReal)) where
  smul a x := ⟨(a : EReal) * (x : EReal), adjoint_mul_mem_Ioi_bot (a : ℝ) a.2 x⟩

/-- Coercing the positive-real action on `]-∞,+∞]` back to `EReal` recovers ordinary
multiplication by the positive scalar. -/
@[simp] theorem posReal_smul_value_apply (a : PosReal) (x : Set.Ioi (⊥ : EReal)) :
    ((a • x : Set.Ioi (⊥ : EReal)) : EReal) = (a : EReal) * (x : EReal) :=
  rfl

/-- Positive-real scaling defines a multiplicative action on `]-∞,+∞]`. -/
noncomputable instance : MulAction PosReal (Set.Ioi (⊥ : EReal)) where
  one_smul x := by
    apply Subtype.ext
    change ((1 : EReal) * (x : EReal)) = (x : EReal)
    simp
  mul_smul a b x := by
    apply Subtype.ext
    simp [mul_assoc, posReal_smul_value_apply]

/-- Coercing the pointwise positive scaling `a • f` back to `EReal` recovers ordinary pointwise
multiplication by `a`. -/
@[simp] theorem posReal_smul_apply (a : PosReal) (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    ((a • f) x : EReal) = (a : EReal) * (f x : EReal) := by
  simp [Pi.smul_apply, posReal_smul_value_apply]

end ERealFunction

namespace Function

/-- The `]-∞,+∞]`-valued function obtained by viewing a real-valued map as finite everywhere. -/
noncomputable def toEReal {X : Type*} (f : X → ℝ) : X → Set.Ioi (⊥ : EReal) :=
  fun x ↦ ⟨(f x : EReal), EReal.bot_lt_coe _⟩

/-- Coercing `f.toEReal` to `EReal` recovers the original real-valued formula. -/
@[simp] theorem toEReal_apply {X : Type*} (f : X → ℝ) (x : X) :
    (f.toEReal x : EReal) = (f x : EReal) :=
  rfl

/-- A real-valued function viewed through `toEReal` is finite everywhere. -/
@[simp] theorem effectiveDomain_toEReal {X : Type*} (f : X → ℝ) :
    ERealFunction.effectiveDomain f.toEReal = Set.univ := by
  ext x
  simp [ERealFunction.effectiveDomain]

/-- Forgetting the `]-∞,+∞]` witness yields the underlying `EReal`-valued function. -/
abbrev asEReal {X : Type*} (f : X → Set.Ioi (⊥ : EReal)) : X → EReal :=
  fun x ↦ (f x : EReal)

/-- Evaluating `asEReal` is just the subtype coercion to `EReal`. -/
@[simp] theorem asEReal_apply {X : Type*} (f : X → Set.Ioi (⊥ : EReal)) (x : X) :
    f.asEReal x = (f x : EReal) :=
  rfl

end Function

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap08/Definition_8_7 -/

namespace ERealFunction

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap08/Proposition_8_4 -/

variable {H : Type u} [AddCommMonoid H] [Module ℝ H]

omit [AddCommMonoid H] [Module ℝ H] in
/-- Every point in the effective domain admits a real height lying above the function value. -/
private lemma exists_real_ge_of_mem_dom (f : H → EReal) {x : H} (hx : x ∈ dom f) :
    ∃ ξ : ℝ, f x ≤ (ξ : EReal) := by
  rw [mem_dom_iff] at hx
  rcases EReal.lt_iff_exists_real_btwn.mp hx with ⟨ξ, hξ, _⟩
  exact ⟨ξ, le_of_lt hξ⟩

omit [AddCommMonoid H] [Module ℝ H] in
/-- A real-height epigraph point has base point in the effective domain. -/
private lemma mem_dom_of_mem_epigraph (f : H → EReal) {x : H} {ξ : ℝ}
    (hξ : (x, ξ) ∈ epigraph f) : x ∈ dom f := by
  rw [mem_epigraph_iff] at hξ
  rw [mem_dom_iff]
  exact lt_of_le_of_lt hξ (EReal.coe_lt_top ξ)

omit [AddCommMonoid H] [Module ℝ H] in
/-- A finite-above and non-`⊥` value gives a canonical real epigraph point via `toReal`. -/
private lemma mem_epigraph_toReal_of_mem_dom_of_ne_bot (f : H → EReal) {x : H} (hx : x ∈ dom f)
    (hbot : f x ≠ ⊥) : (x, (f x).toReal) ∈ epigraph f := by
  have htop : f x ≠ ⊤ := ne_of_lt ((mem_dom_iff f x).mp hx)
  simp [mem_epigraph_iff, EReal.coe_toReal htop hbot]

/-- If the left endpoint takes value `-∞`, convexity of the epigraph forces every strict convex
combination with a finite point to take value `-∞` as well. -/
private lemma combo_value_eq_bot_of_left_bot_of_convex_epigraph (f : H → EReal)
    (hconv : Convex ℝ (epigraph f)) {x y : H} (hfx : f x = ⊥) (hy : y ∈ dom f) {α : ℝ}
    (hα : 0 < α) (hα_lt_one : α < 1) :
    f (α • x + (1 - α) • y) = ⊥ := by
  refine (EReal.eq_bot_iff_forall_lt _).2 ?_
  intro r
  rcases exists_real_ge_of_mem_dom f hy with ⟨ξ, hξ⟩
  let η : ℝ := (r - (1 - α) * ξ) / α - 1
  have hx_mem : (x, η) ∈ epigraph f := by
    rw [mem_epigraph_iff, hfx]
    simp
  have hy_mem : (y, ξ) ∈ epigraph f := by
    simpa [mem_epigraph_iff] using hξ
  have hβ : 0 < 1 - α := sub_pos.mpr hα_lt_one
  have hcombo_mem :
      (α • (x, η) + (1 - α) • (y, ξ)) ∈ epigraph f := by
    exact (convex_iff_forall_pos.mp hconv) hx_mem hy_mem hα hβ (by ring)
  have hcombo_le :
      f (α • x + (1 - α) • y) ≤ ((α * η + (1 - α) * ξ : ℝ) : EReal) := by
    rw [mem_epigraph_iff] at hcombo_mem
    simpa [Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hcombo_mem
  have hη_eq : α * η + (1 - α) * ξ = r - α := by
    dsimp [η]
    field_simp [hα.ne']
    ring
  have hheight_lt : ((α * η + (1 - α) * ξ : ℝ) : EReal) < (r : EReal) := by
    rw [hη_eq]
    exact EReal.coe_lt_coe_iff.mpr (sub_lt_self _ hα)
  exact lt_of_le_of_lt hcombo_le hheight_lt

/-- Proposition 8.4: the real-height epigraph of an extended-real-valued function is convex if and
only if Jensen's inequality holds for every two points of the effective domain `dom f = {x | f x <
⊤}` and every coefficient `α ∈ ]0,1[`. -/
theorem convex_epigraph_iff_jensen_on_dom (f : H → EReal) :
    Convex ℝ (epigraph f) ↔
      ∀ ⦃x y : H⦄, x ∈ dom f → y ∈ dom f → ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
        f (α • x + (1 - α) • y) ≤
          (α : EReal) * f x + (((1 - α : ℝ) : EReal) * f y) := by
  constructor
  · intro hconv x y hx hy α hα hα_lt_one
    by_cases hfx : f x = ⊥
    · have hcombo_bot :
          f (α • x + (1 - α) • y) = ⊥ :=
        combo_value_eq_bot_of_left_bot_of_convex_epigraph f hconv hfx hy hα hα_lt_one
      have hαE : 0 < (α : EReal) := by
        exact EReal.coe_pos.mpr hα
      simp [hcombo_bot, hfx, EReal.mul_bot_of_pos hαE]
    · by_cases hfy : f y = ⊥
      · have hcombo_bot_swapped :
            f ((1 - α) • y + (1 - (1 - α)) • x) = ⊥ :=
          combo_value_eq_bot_of_left_bot_of_convex_epigraph f hconv hfy hx
            (sub_pos.mpr hα_lt_one) (by linarith)
        have hrewrite : 1 - (1 - α) = α := by ring
        have hcombo_bot :
            f (α • x + (1 - α) • y) = ⊥ := by
          simpa [hrewrite, add_comm, add_left_comm, add_assoc] using hcombo_bot_swapped
        have hβE : 0 < ((1 - α : ℝ) : EReal) := by
          exact EReal.coe_pos.mpr (sub_pos.mpr hα_lt_one)
        simp [hcombo_bot, hfy]
      · have hx_mem : (x, (f x).toReal) ∈ epigraph f :=
          mem_epigraph_toReal_of_mem_dom_of_ne_bot f hx hfx
        have hy_mem : (y, (f y).toReal) ∈ epigraph f :=
          mem_epigraph_toReal_of_mem_dom_of_ne_bot f hy hfy
        have hβ : 0 < 1 - α := sub_pos.mpr hα_lt_one
        have hcombo_mem :
            (α • (x, (f x).toReal) + (1 - α) • (y, (f y).toReal)) ∈ epigraph f := by
          exact (convex_iff_forall_pos.mp hconv) hx_mem hy_mem hα hβ (by ring)
        have hcombo_le :
            f (α • x + (1 - α) • y) ≤
              ((α * (f x).toReal + (1 - α) * (f y).toReal : ℝ) : EReal) := by
          rw [mem_epigraph_iff] at hcombo_mem
          simpa [Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hcombo_mem
        have hxtop : f x ≠ ⊤ := ne_of_lt ((mem_dom_iff f x).mp hx)
        have hytop : f y ≠ ⊤ := ne_of_lt ((mem_dom_iff f y).mp hy)
        calc
          f (α • x + (1 - α) • y)
              ≤ ((α * (f x).toReal + (1 - α) * (f y).toReal : ℝ) : EReal) := hcombo_le
          _ = (α : EReal) * f x + (((1 - α : ℝ) : EReal) * f y) := by
            rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul, EReal.coe_toReal hxtop hfx,
              EReal.coe_toReal hytop hfy]
  · intro hJ
    refine (convex_iff_forall_pos).2 ?_
    intro p hp q hq a b ha hb hab
    rcases p with ⟨x, ξ⟩
    rcases q with ⟨y, η⟩
    have hx : x ∈ dom f := mem_dom_of_mem_epigraph f hp
    have hy : y ∈ dom f := mem_dom_of_mem_epigraph f hq
    have ha_lt_one : a < 1 := by nlinarith
    have hb_eq : b = 1 - a := by nlinarith
    have haE : 0 < (a : EReal) := EReal.coe_pos.mpr ha
    have hbE : 0 < (b : EReal) := EReal.coe_pos.mpr hb
    have hJxy :
        f (a • x + b • y) ≤ (a : EReal) * f x + ((b : EReal) * f y) := by
      simpa [hb_eq] using hJ hx hy ha ha_lt_one
    have hx_le :
        (a : EReal) * f x ≤ (a : EReal) * (ξ : EReal) :=
      mul_le_mul_of_nonneg_left ((mem_epigraph_iff f x ξ).mp hp) haE.le
    have hy_le :
        (b : EReal) * f y ≤ (b : EReal) * (η : EReal) :=
      mul_le_mul_of_nonneg_left ((mem_epigraph_iff f y η).mp hq) hbE.le
    have hsum_le :
        (a : EReal) * f x + (b : EReal) * f y ≤
          (a : EReal) * (ξ : EReal) + (b : EReal) * (η : EReal) :=
      add_le_add hx_le hy_le
    have hfinal :
        f (a • x + b • y) ≤ ((a * ξ + b * η : ℝ) : EReal) := by
      calc
        f (a • x + b • y)
            ≤ (a : EReal) * f x + (b : EReal) * f y := hJxy
        _ ≤ (a : EReal) * (ξ : EReal) + (b : EReal) * (η : EReal) := hsum_le
        _ = ((a * ξ + b * η : ℝ) : EReal) := by
          rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    rw [mem_epigraph_iff]
    simpa [Prod.smul_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hfinal

section RealVectorSpace

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- Definition 8.7 (1): a proper `]-∞,+∞]`-valued function is strictly convex when the strict
Jensen inequality holds on its effective domain for every distinct pair of domain points and every
coefficient `α ∈ ]0,1[`. -/
def StrictlyConvex (f : H → Set.Ioi (⊥ : EReal)) : Prop :=
  ∀ ⦃x : H⦄, x ∈ effectiveDomain f → ∀ ⦃y : H⦄, y ∈ effectiveDomain f → x ≠ y →
    ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
      (f (α • x + (1 - α) • y) : EReal) <
        (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal)

/-- Definition 8.7 (2): a proper `]-∞,+∞]`-valued function is convex on a nonempty subset `C` of
its effective domain when Jensen's inequality holds for every pair of points of `C` and every
coefficient `α ∈ ]0,1[`. -/
def ConvexOn (f : H → Set.Ioi (⊥ : EReal)) (C : Set H) : Prop :=
  C.Nonempty ∧ C ⊆ effectiveDomain f ∧
    ∀ ⦃x : H⦄, x ∈ C → ∀ ⦃y : H⦄, y ∈ C → ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
      (f (α • x + (1 - α) • y) : EReal) ≤
        (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal)

/-- Definition 8.7 (3): a proper `]-∞,+∞]`-valued function is strictly convex on a nonempty subset
`C` of its effective domain when the strict Jensen inequality holds on `C` for distinct points and
every coefficient `α ∈ ]0,1[`. -/
def StrictlyConvexOn (f : H → Set.Ioi (⊥ : EReal)) (C : Set H) : Prop :=
  C.Nonempty ∧ C ⊆ effectiveDomain f ∧
    ∀ ⦃x : H⦄, x ∈ C → ∀ ⦃y : H⦄, y ∈ C → x ≠ y → ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
      (f (α • x + (1 - α) • y) : EReal) <
        (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal)

/-- A strictly convex function satisfies the strict Jensen inequality at any two distinct
effective-domain points. -/
theorem StrictlyConvex.ineq {f : H → Set.Ioi (⊥ : EReal)} (hf : StrictlyConvex f)
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) (hxy : x ≠ y)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (f (α • x + (1 - α) • y) : EReal) <
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
  simpa [StrictlyConvex] using hf hx hy hxy hα0 hα1

/-- Restricting a strictly convex function to a nonempty subset of its effective domain yields a
strictly convex-on function. -/
theorem StrictlyConvex.strictlyConvexOn {f : H → Set.Ioi (⊥ : EReal)} {C : Set H}
    (hf : StrictlyConvex f) (hC_nonempty : C.Nonempty) (hC_dom : C ⊆ effectiveDomain f) :
    StrictlyConvexOn f C := by
  refine ⟨hC_nonempty, hC_dom, ?_⟩
  intro x hx y hy hxy α hα0 hα1
  exact hf.ineq (hC_dom hx) (hC_dom hy) hxy hα0 hα1

/-- A convex-on set is nonempty. -/
theorem ConvexOn.nonempty {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} (hf : ConvexOn f C) :
    C.Nonempty := by
  exact hf.1

/-- A convex-on set is contained in the effective domain. -/
theorem ConvexOn.subset_effectiveDomain {f : H → Set.Ioi (⊥ : EReal)} {C : Set H}
    (hf : ConvexOn f C) : C ⊆ effectiveDomain f := by
  exact hf.2.1

/-- A function convex on `C` satisfies Jensen's inequality for points of `C`. -/
theorem ConvexOn.ineq {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} (hf : ConvexOn f C)
    {x y : H} (hx : x ∈ C) (hy : y ∈ C) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (f (α • x + (1 - α) • y) : EReal) ≤
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
  exact hf.2.2 hx hy hα0 hα1

/-- A convex function on its effective domain has a convex effective domain. -/
theorem ConvexOn.convex_effectiveDomain {f : H → Set.Ioi (⊥ : EReal)}
    (hf : ConvexOn f (effectiveDomain f)) :
    Convex ℝ (effectiveDomain f) := by
  refine (convex_iff_forall_pos).2 ?_
  intro x hx y hy a b ha hb hab
  have ha_lt_one : a < 1 := by
    linarith
  have hsub_cast : (((1 - a : ℝ) : EReal)) = 1 - (a : EReal) := by
    rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
  have hb_eq : (1 - a : ℝ) = b := by
    linarith
  have hineq₀ := hf.ineq hx hy ha ha_lt_one
  have hineq₁ :
      (f (a • x + (1 - a) • y) : EReal) ≤
        (a : EReal) * (f x : EReal) + (((1 - a : ℝ) : EReal) * (f y : EReal)) := by
    simpa [hsub_cast] using hineq₀
  have hineq :
      (f (a • x + b • y) : EReal) ≤
        (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) := by
    simpa [hb_eq] using hineq₁
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hsum :
      (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) =
        ((a * (f x : EReal).toReal + b * (f y : EReal).toReal : ℝ) : EReal) := by
    rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hy_top hy_bot,
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    simp
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt (hineq.trans_eq hsum) (EReal.coe_lt_top _)

/-- A function convex on its effective domain has convex real-height epigraph. -/
theorem ConvexOn.convex_epigraph_asEReal {f : H → Set.Ioi (⊥ : EReal)}
    (hf : ConvexOn f (effectiveDomain f)) :
    Convex ℝ (epigraph f.asEReal) := by
  refine (convex_epigraph_iff_jensen_on_dom f.asEReal).2 ?_
  intro x y hx hy α hα0 hα1
  have hx' : x ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using hx
  have hy' : y ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using hy
  simpa using hf.ineq hx' hy' hα0 hα1

/-- The finite representative of a convex function is mathlib-convex on its effective domain. -/
theorem ConvexOn.toReal_convexOn_effectiveDomain {f : H → Set.Ioi (⊥ : EReal)}
    (hf : ConvexOn f (effectiveDomain f)) :
    _root_.ConvexOn ℝ (effectiveDomain f) (fun x ↦ (f x : EReal).toReal) := by
  rw [convexOn_iff_forall_pos]
  constructor
  · exact hf.convex_effectiveDomain
  · intro x hx y hy a b ha hb hab
    have ha_lt_one : a < 1 := by
      linarith
    have hsub_cast : (((1 - a : ℝ) : EReal)) = 1 - (a : EReal) := by
      rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
    have hb_eq : (1 - a : ℝ) = b := by
      linarith
    have hineq₀ := hf.ineq hx hy ha ha_lt_one
    have hineq₁ :
        (f (a • x + (1 - a) • y) : EReal) ≤
          (a : EReal) * (f x : EReal) + (((1 - a : ℝ) : EReal) * (f y : EReal)) := by
      simpa [hsub_cast] using hineq₀
    have hineq :
        (f (a • x + b • y) : EReal) ≤
          (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) := by
      simpa [hb_eq] using hineq₁
    have hxy : a • x + b • y ∈ effectiveDomain f :=
      hf.convex_effectiveDomain hx hy ha.le hb.le hab
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hy_bot : (f y : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
    have hxy_bot : (f (a • x + b • y) : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f (a • x + b • y) : EReal) from
        (f (a • x + b • y)).2)
    have hsum :
        (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) =
          ((a * (f x : EReal).toReal + b * (f y : EReal).toReal : ℝ) : EReal) := by
      rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hy_top hy_bot,
        ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      simp
    have hright_top :
        (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) ≠ ⊤ := by
      rw [hsum]
      exact ne_of_lt (EReal.coe_lt_top _)
    simpa [hsum] using EReal.toReal_le_toReal hineq hxy_bot hright_top

/-- A strictly convex-on set is nonempty. -/
theorem StrictlyConvexOn.nonempty {f : H → Set.Ioi (⊥ : EReal)} {C : Set H}
    (hf : StrictlyConvexOn f C) : C.Nonempty := by
  exact hf.1

/-- A strictly convex-on set is contained in the effective domain. -/
theorem StrictlyConvexOn.subset_effectiveDomain {f : H → Set.Ioi (⊥ : EReal)} {C : Set H}
    (hf : StrictlyConvexOn f C) : C ⊆ effectiveDomain f := by
  exact hf.2.1

/-- A function strictly convex on `C` satisfies the strict Jensen inequality for distinct points of
`C`. -/
theorem StrictlyConvexOn.ineq {f : H → Set.Ioi (⊥ : EReal)} {C : Set H}
    (hf : StrictlyConvexOn f C) {x y : H} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    (f (α • x + (1 - α) • y) : EReal) <
      (α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal) := by
  exact hf.2.2 hx hy hxy hα0 hα1

/-- Restricting a strictly convex-on function to a nonempty subset preserves strict convexity. -/
theorem StrictlyConvexOn.mono {f : H → Set.Ioi (⊥ : EReal)} {C D : Set H}
    (hf : StrictlyConvexOn f D) (hC_nonempty : C.Nonempty) (hC_subset : C ⊆ D) :
    StrictlyConvexOn f C := by
  refine ⟨hC_nonempty, fun x hx ↦ hf.subset_effectiveDomain (hC_subset hx), ?_⟩
  intro x hx y hy hxy α hα0 hα1
  exact hf.ineq (hC_subset hx) (hC_subset hy) hxy hα0 hα1

end RealVectorSpace

end ERealFunction

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap01/Text_1_0_18 -/

namespace EReal

/-- Real scalars act on extended reals by multiplication. -/
noncomputable instance : SMul ℝ EReal := ⟨fun a x ↦ (a : EReal) * x⟩

/-- Coercing a real scalar action on `EReal` to multiplication. -/
@[simp] theorem real_smul_def (a : ℝ) (x : EReal) : a • x = (a : EReal) * x :=
  rfl

end EReal
