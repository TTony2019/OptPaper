import Mathlib
import Foundation.Analysis.ExtendedRealFunctions
import Foundation.Convex.Gamma0
import Foundation.Convex.ArgminExistence
import Foundation.Convex.ProximalOperator

/-!
# Fenchel conjugation

The Fenchel conjugate `f∗` of an extended-real-valued function, the reflection
`fᵛ`, the Fenchel–Young inequality, and the fact that the conjugate of any
function belongs to `Γ(H)`.
-/

open scoped InnerProductSpace

universe u

namespace ERealFunction

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap13/Definition_13_1 -/

section Reflection

variable {H : Type u} [AddGroup H]

/-- The reflection of an extended-real-valued function is the precomposition `x ↦ f (-x)`. -/
def reverse (f : H → EReal) : H → EReal :=
  fun x ↦ f (-x)

/- Lean cannot use the textbook ASCII surface `f^∨` here. We therefore use the postfix vee token
`fᵛ` as the direct Lean surface for function reversal. -/
scoped postfix:max "ᵛ" => ERealFunction.reverse

/-- Evaluating the reflection rewrites it as the pointwise formula `f (-x)`. -/
@[simp] theorem reverse_apply (f : H → EReal) (x : H) :
    fᵛ x = f (-x) :=
  rfl

end Reflection

namespace Function

section Reflection

variable {H : Type u} [AddGroup H]

/-- The reflection of an `]-∞,+∞]`-valued function is the precomposition `x ↦ f (-x)`. -/
def reverse (f : H → Set.Ioi (⊥ : EReal)) : H → Set.Ioi (⊥ : EReal) :=
  fun x ↦ f (-x)

/- Lean cannot use the textbook ASCII surface `f^∨` here either. We therefore reuse the postfix
vee token `fᵛ` as the direct Lean surface for reflection on `]-∞,+∞]`-valued functions. -/
scoped postfix:max "ᵛ" => Function.reverse

/-- Evaluating the reflection rewrites it as the pointwise formula `f (-x)`. -/
@[simp] theorem reverse_apply (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    fᵛ x = f (-x) :=
  rfl

end Reflection

end Function

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Definition 13.1: the conjugate of an extended-real-valued function on a real inner-product
space is the function `u ↦ sup_x (⟪x, u⟫ - f x)`. -/
noncomputable def conjugate (f : H → EReal) : H → EReal :=
  fun u ↦ ⨆ x : H, ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x

/- Lean cannot use the textbook ASCII surface `f^*` here: `^` is exponent syntax and `*` is the
multiplicative token. We therefore use the postfix star token `f∗` as the direct Lean surface for
Fenchel conjugation, so `f∗∗` is the biconjugate. -/
scoped postfix:max "∗" => ERealFunction.conjugate

/-- Evaluating the conjugate rewrites it as the supremum of the affine defects
`x ↦ ⟪x, u⟫ - f x`. -/
@[simp] theorem conjugate_apply (f : H → EReal) (u : H) :
    f∗ u = ⨆ x : H, ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x :=
  rfl

/-- Evaluating the conjugate with the linear functional in the first
inner-product slot: `f∗ u = sup_x (⟪u, x⟫ - f x)`. -/
theorem conjugate_apply_swap (f : H → EReal) (u : H) :
    f∗ u = ⨆ x : H, ((⟪u, x⟫_ℝ : ℝ) : EReal) - f x := by
  rw [conjugate_apply]
  apply le_antisymm
  · apply iSup_le
    intro x
    rw [real_inner_comm u x]
    exact le_iSup (fun v : H => ((⟪u, v⟫_ℝ : ℝ) : EReal) - f v) x
  · apply iSup_le
    intro x
    rw [real_inner_comm x u]
    exact le_iSup (fun v : H => ((⟪v, u⟫_ℝ : ℝ) : EReal) - f v) x

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap09/Proposition_9_3 -/

end Conjugation

section SupremumGamma

variable {H : Type u} [TopologicalSpace H] [SequentialSpace H] [AddCommGroup H] [Module ℝ H]
variable {I : Type v}

/-- Helper for Proposition 9.3: a weighted pointwise supremum is bounded by the corresponding
weighted sum of the separate suprema when the weights are nonnegative. -/
lemma weighted_iSup_le_weighted_iSup {u v : I → EReal} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (⨆ i, (a : EReal) * u i + (b : EReal) * v i) ≤
      (a : EReal) * (⨆ i, u i) + (b : EReal) * (⨆ i, v i) := by
  have haE : (0 : EReal) ≤ (a : EReal) := by
    exact_mod_cast ha
  have hbE : (0 : EReal) ≤ (b : EReal) := by
    exact_mod_cast hb
  have hu : (⨆ i, (a : EReal) * u i) ≤ (a : EReal) * (⨆ i, u i) := by
    refine iSup_le fun i ↦ ?_
    exact mul_le_mul_of_nonneg_left (le_iSup u i) haE
  have hv : (⨆ i, (b : EReal) * v i) ≤ (b : EReal) * (⨆ i, v i) := by
    refine iSup_le fun i ↦ ?_
    exact mul_le_mul_of_nonneg_left (le_iSup v i) hbE
  calc
    (⨆ i, (a : EReal) * u i + (b : EReal) * v i)
        ≤ (⨆ i, (a : EReal) * u i) + ⨆ i, (b : EReal) * v i := EReal.iSup_add_le_add_iSup
    _ ≤ (a : EReal) * (⨆ i, u i) + (b : EReal) * (⨆ i, v i) := add_le_add hu hv

/-- Helper for Proposition 9.3: the pointwise supremum of Jensen-convex extended-real-valued
functions is Jensen-convex. -/
lemma isConvex_iSup_of_isConvex (f : I → H → EReal) (hf : ∀ i, IsConvex (f i)) :
    IsConvex (fun x ↦ ⨆ i, f i x) := by
  intro x y a ha0 ha1
  have hpointwise :
      (⨆ i, f i (a • x + (1 - a) • y)) ≤
        ⨆ i, (a : EReal) * f i x + (1 - a : EReal) * f i y := by
    refine iSup_le fun i ↦ ?_
    exact (hf i ha0 ha1).trans
      (le_iSup (fun i ↦ (a : EReal) * f i x + (1 - a : EReal) * f i y) i)
  have hone_sub : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  calc
    (⨆ i, f i (a • x + (1 - a) • y))
        ≤ ⨆ i, (a : EReal) * f i x + (1 - a : EReal) * f i y := hpointwise
    _ ≤ (a : EReal) * (⨆ i, f i x) + (1 - a : EReal) * (⨆ i, f i y) :=
      weighted_iSup_le_weighted_iSup ha0 hone_sub

/-- Helper for Proposition 9.3: the pointwise supremum of a family in `gamma H` is lower
semicontinuous. -/
lemma lowerSemicontinuous_iSup_of_mem_gamma (f : I → H → EReal) (hf : ∀ i, f i ∈ gamma H) :
    LowerSemicontinuous (fun x ↦ ⨆ i, f i x) := by
  refine lowerSemicontinuous_iSup fun i ↦ ?_
  exact (mem_gamma_iff (f i)).mp (hf i) |>.2

/-- Proposition 9.3: the pointwise supremum of a family of functions in `Γ(ℋ)` again belongs to
`Γ(ℋ)`. -/
theorem iSup_mem_gamma (f : I → H → EReal)
    (hf : ∀ i, f i ∈ gamma H) :
    (fun x ↦ ⨆ i, f i x) ∈ gamma H := by
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · exact isConvex_iSup_of_isConvex f fun i ↦ (mem_gamma_iff (f i)).mp (hf i) |>.1
  · exact lowerSemicontinuous_iSup_of_mem_gamma f hf

end SupremumGamma

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap09/Proposition_9_5 -/

section CompLinearMap

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- Precomposing a member of `gamma K` with a continuous linear map yields a member of `gamma H`. -/
theorem mem_gamma_comp_continuousLinearMap
    (f : K → EReal) (L : H →L[ℝ] K) (hf : f ∈ gamma K) :
    f ∘ L ∈ gamma H := by
  rw [mem_gamma_iff] at hf ⊢
  rcases hf with ⟨hf_convex, hf_lsc⟩
  refine ⟨?_, ?_⟩
  · intro x y a ha0 ha1
    simpa [Function.comp] using
      hf_convex (x := L x) (y := L y) (a := a) ha0 ha1
  · exact hf_lsc.comp L.continuous

end CompLinearMap

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap13/Proposition_13_13 -/

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem real_affine_mem_gamma (c : ℝ) :
    (fun t : ℝ ↦ ((t - c : ℝ) : EReal)) ∈ gamma ℝ := by
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · intro x y a ha0 ha1
    change (((a * x + (1 - a) * y - c : ℝ) : ℝ) : EReal) ≤
      (a : EReal) * ((x - c : ℝ) : EReal) + (1 - a : EReal) * ((y - c : ℝ) : EReal)
    exact le_of_eq <| by
      have hreal : a * x + (1 - a) * y - c = a * (x - c) + (1 - a) * (y - c) := by
        ring
      exact_mod_cast hreal
  · simpa [Function.comp] using
      (continuous_coe_real_ereal.comp (continuous_id.sub continuous_const)).lowerSemicontinuous

private theorem affineDefect_mem_gamma (f : H → EReal) (x : H) :
    (fun u : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) ∈ gamma H := by
  by_cases htop : f x = ⊤
  · have hbot_const : (fun _ : H ↦ (⊥ : EReal)) ∈ gamma H := by
      rw [mem_gamma_iff]
      refine ⟨?_, ?_⟩
      · intro y z a ha0 ha1
        simp
      · simpa using (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : H ↦ (⊥ : EReal)))
    simpa [htop] using hbot_const
  by_cases hbot : f x = ⊥
  · have htop_const : (fun _ : H ↦ (⊤ : EReal)) ∈ gamma H := by
      rw [mem_gamma_iff]
      refine ⟨?_, ?_⟩
      · intro y z a ha0 ha1
        by_cases h0 : a = 0
        · subst h0
          simp
        by_cases h1 : a = 1
        · subst h1
          rw [show (1 - (1 : ℝ) : EReal) = 0 by
                simpa using
                  EReal.sub_self (EReal.coe_ne_top 1) (EReal.coe_ne_bot 1)]
          simp
        have ha_pos : 0 < a := lt_of_le_of_ne ha0 fun h ↦ h0 h.symm
        have hb_pos : 0 < 1 - a := sub_pos.mpr (lt_of_le_of_ne ha1 h1)
        rw [EReal.mul_top_of_pos (by exact_mod_cast ha_pos),
          EReal.mul_top_of_pos (by exact_mod_cast hb_pos)]
        simp
      · simpa using (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : H ↦ (⊤ : EReal)))
    simpa [hbot] using htop_const
  have hcomp :=
    mem_gamma_comp_continuousLinearMap
      (fun t : ℝ ↦ ((t - (f x).toReal : ℝ) : EReal))
      (innerSL ℝ x)
      (real_affine_mem_gamma (f x).toReal)
  have hrewrite :
      (fun u : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) =
        fun u : H ↦ ((⟪x, u⟫_ℝ - (f x).toReal : ℝ) : EReal) := by
    ext u
    rw [← EReal.coe_toReal htop hbot]
    simp
  rw [hrewrite]
  simpa [Function.comp, innerSL_apply_apply, real_inner_comm] using hcomp

/-- Proposition 13.13: the Fenchel conjugate of an extended-real-valued function on a real
inner-product space belongs to the textbook class `Γ(H)` of convex lower semicontinuous
functions. -/
theorem conjugate_mem_gamma (f : H → EReal) :
    f∗ ∈ gamma H := by
  simpa [conjugate_apply] using
    iSup_mem_gamma
      (fun x u ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x)
      (affineDefect_mem_gamma f)

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap13/Proposition_13_15 -/

/-- The Fenchel conjugate of a proper extended-real-valued function never takes the value `-∞`. -/
theorem conjugate_ne_bot_of_isProper
    {f : H → EReal} (hproper : IsProper f) (u : H) :
    f∗ u ≠ ⊥ := by
  rcases hproper.2 with ⟨x, hx⟩
  have hxtop : f x ≠ ⊤ := mem_dom_iff_ne_top.mp hx
  have hterm : (((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) ≠ ⊥ := by
    cases hfx : f x with
    | bot => simp
    | top => exact (hxtop hfx).elim
    | coe r => simpa using (EReal.coe_ne_bot (⟪x, u⟫_ℝ - r))
  intro hconj
  apply hterm
  exact le_bot_iff.mp <| hconj ▸ by
    rw [conjugate_apply]
    exact le_iSup (fun y : H ↦ ((⟪y, u⟫_ℝ : ℝ) : EReal) - f y) x

/-- Proposition 13.15: for a proper extended-real-valued function on a real inner-product space,
the Fenchel--Young inequality states that `f x + f*(u)` dominates the pairing `⟪x, u⟫`. -/
theorem fenchel_young_inequality
    {f : H → EReal} (hproper : IsProper f) (x u : H) :
    ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ f x + f∗ u := by
  by_cases htop : f x = ⊤
  · have hsum : f x + f∗ u = ⊤ := by
      rw [htop]
      exact EReal.top_add_of_ne_bot (conjugate_ne_bot_of_isProper hproper u)
    rw [hsum]
    exact le_top
  · rw [conjugate_apply]
    simpa [add_comm] using
      (EReal.sub_le_iff_le_add (.inl (hproper.1 x)) (.inl htop)).1 <|
        le_iSup (fun y : H ↦ ((⟪y, u⟫_ℝ : ℝ) : EReal) - f y) x

end Conjugation

end ERealFunction

namespace ERealFunction

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap07/Corollary_7_12 -/

section Separation

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

/-- Helper for Corollary 7.12: a point outside a closed convex set is excluded by some real closed
halfspace that still contains the set. -/
lemma exists_closedHalfspace_separating_of_not_mem_of_isClosed_of_convex
    {C : Set 𝓗} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) {x : 𝓗} (hx : x ∉ C) :
    ∃ u : 𝓗, ∃ η : ℝ,
      C ⊆ {y : 𝓗 | ⟪y, u⟫_ℝ ≤ η} ∧ x ∉ {y : 𝓗 | ⟪y, u⟫_ℝ ≤ η} := by
  obtain ⟨f, η, hC_lt, hx_lt⟩ := geometric_hahn_banach_closed_point hC_convex hC_closed hx
  let u : 𝓗 := (InnerProductSpace.toDual ℝ 𝓗).symm f
  refine ⟨u, η, ?_, ?_⟩
  · intro y hyC
    have hy_le : f y ≤ η := (hC_lt y hyC).le
    have hy_inner : ⟪u, y⟫_ℝ ≤ η := by
      simpa [u] using hy_le
    simpa [real_inner_comm] using hy_inner
  · intro hx_mem
    have hx_le : f x ≤ η := by
      have hx_inner : ⟪u, x⟫_ℝ ≤ η := by
        simpa [real_inner_comm] using hx_mem
      simpa [u] using hx_inner
    exact (not_le_of_gt hx_lt) hx_le

end Separation

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap09/Definition_9_7 -/

section ConvexEnvelope

variable {H : Type u} [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]

/-- The lower semicontinuous convex minorants of an extended-real-valued function. -/
def lowerSemicontinuousConvexMinorants (f : H → EReal) : Set (H → EReal) :=
  {g | LowerSemicontinuous g ∧ Convex ℝ (epigraph g) ∧ g ≤ f}

/-- A function is a lower semicontinuous convex minorant of `f` exactly when it is lower
semicontinuous, has convex epigraph, and is pointwise dominated by `f`. -/
theorem mem_lowerSemicontinuousConvexMinorants_iff (f g : H → EReal) :
    g ∈ lowerSemicontinuousConvexMinorants f ↔
      LowerSemicontinuous g ∧ Convex ℝ (epigraph g) ∧ g ≤ f := by
  rfl

/-- Definition 9.7: the lower semicontinuous convex envelope of `f` is the supremum, in the
function lattice, of all lower semicontinuous convex minorants of `f`. -/
noncomputable def lowerSemicontinuousConvexEnvelope (f : H → EReal) : H → EReal :=
  sSup (lowerSemicontinuousConvexMinorants f)

/-- The lower semicontinuous convex envelope is computed pointwise as the supremum of the values of
all lower semicontinuous convex minorants of `f` at that point. -/
theorem lowerSemicontinuousConvexEnvelope_apply (f : H → EReal) (x : H) :
    lowerSemicontinuousConvexEnvelope f x =
      sSup ((fun g : H → EReal ↦ g x) '' lowerSemicontinuousConvexMinorants f) := by
  change sSup (lowerSemicontinuousConvexMinorants f) x =
    sSup ((fun g : H → EReal ↦ g x) '' lowerSemicontinuousConvexMinorants f)
  exact sSup_apply_eq_sSup_image

/-- The lower semicontinuous convex envelope is the pointwise supremum of its indexed minorants. -/
private theorem lowerSemicontinuousConvexEnvelope_eq_iSup_minorants (f : H → EReal) :
    lowerSemicontinuousConvexEnvelope f =
      fun x ↦ ⨆ g : {g : H → EReal // g ∈ lowerSemicontinuousConvexMinorants f}, g.1 x := by
  funext x
  rw [lowerSemicontinuousConvexEnvelope_apply]
  apply le_antisymm
  · refine sSup_le fun y hy ↦ ?_
    rcases hy with ⟨g, hg, rfl⟩
    exact le_iSup_of_le ⟨g, hg⟩ le_rfl
  · refine iSup_le fun g ↦ ?_
    exact le_sSup ⟨g.1, g.2, rfl⟩

/-- Proposition 9.8 (1): the lower semicontinuous convex envelope is pointwise majorized by `f`. -/
theorem lowerSemicontinuousConvexEnvelope_le (f : H → EReal) :
    lowerSemicontinuousConvexEnvelope f ≤ f := by
  intro x
  rw [lowerSemicontinuousConvexEnvelope_eq_iSup_minorants]
  exact iSup_le fun g ↦ ((mem_lowerSemicontinuousConvexMinorants_iff f g.1).mp g.2).2.2 x

/-- Proposition 9.8 (2): the lower semicontinuous convex envelope is lower semicontinuous. -/
theorem lowerSemicontinuous_lowerSemicontinuousConvexEnvelope (f : H → EReal) :
    LowerSemicontinuous (lowerSemicontinuousConvexEnvelope f) := by
  simpa [lowerSemicontinuousConvexEnvelope_eq_iSup_minorants] using
    (lowerSemicontinuous_iSup fun g :
        {g : H → EReal // g ∈ lowerSemicontinuousConvexMinorants f} ↦
      ((mem_lowerSemicontinuousConvexMinorants_iff f g.1).mp g.2).1)

/-- Proposition 9.8 (3): the epigraph of the lower semicontinuous convex envelope is convex. -/
theorem convex_epigraph_lowerSemicontinuousConvexEnvelope (f : H → EReal) :
    Convex ℝ (epigraph (lowerSemicontinuousConvexEnvelope f)) := by
  have hEq :
      (⨆ g : {g : H → EReal // g ∈ lowerSemicontinuousConvexMinorants f}, g.1) =
        fun x ↦ ⨆ g : {g : H → EReal // g ∈ lowerSemicontinuousConvexMinorants f}, g.1 x := by
    funext x
    simp [iSup_apply]
  have hconv :
      Convex ℝ
        (epigraph (⨆ g : {g : H → EReal // g ∈ lowerSemicontinuousConvexMinorants f}, g.1)) := by
    rw [epigraph_iSup]
    exact convex_iInter fun g ↦ ((mem_lowerSemicontinuousConvexMinorants_iff f g.1).mp g.2).2.1
  rw [lowerSemicontinuousConvexEnvelope_eq_iSup_minorants, ← hEq]
  exact hconv

/-- Proposition 9.8 (4): every lower semicontinuous convex minorant of `f` lies below the lower
semicontinuous convex envelope. -/
theorem le_lowerSemicontinuousConvexEnvelope_of_lowerSemicontinuous_of_convex_epigraph
    {f g : H → EReal} (hg_lsc : LowerSemicontinuous g) (hg_conv : Convex ℝ (epigraph g))
    (hg_le : g ≤ f) :
    g ≤ lowerSemicontinuousConvexEnvelope f := by
  intro x
  rw [lowerSemicontinuousConvexEnvelope_eq_iSup_minorants]
  exact le_iSup_of_le
    ⟨g, (mem_lowerSemicontinuousConvexMinorants_iff f g).mpr ⟨hg_lsc, hg_conv, hg_le⟩⟩
    le_rfl

end ConvexEnvelope

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap09/Proposition_9_18 (product bridge) -/

section ProductBridge

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Canonical raw-product `ℓ²` seminorm bridge on `H × ℝ`, matching the textbook Hilbert geometry
used for epigraph projections. -/
noncomputable abbrev prod_seminormedAddCommGroup_l2_real : SeminormedAddCommGroup (H × ℝ) :=
  WithLp.seminormedAddCommGroupToProd (p := 2) (α := H) (β := ℝ)

/-- Canonical raw-product `ℓ²` norm bridge on `H × ℝ`. -/
noncomputable abbrev prod_normedAddCommGroup_l2_real : NormedAddCommGroup (H × ℝ) :=
  WithLp.normedAddCommGroupToProd (p := 2) (α := H) (β := ℝ)

/-- Canonical raw-product `ℓ²` scalar-action bridge on `H × ℝ`. -/
noncomputable abbrev prod_normedSpace_l2_real : @NormedSpace ℝ (H × ℝ) _ (prod_seminormedAddCommGroup_l2_real (H := H)) := by
  letI : SeminormedAddCommGroup (H × ℝ) := prod_seminormedAddCommGroup_l2_real (H := H)
  letI : NormedAddCommGroup (H × ℝ) := prod_normedAddCommGroup_l2_real (H := H)
  exact WithLp.normedSpaceSeminormedAddCommGroupToProd (p := 2) (α := H) (β := ℝ) (R := ℝ)

/-- Canonical raw-product `ℓ²` completeness bridge on `H × ℝ`. -/
noncomputable abbrev prod_completeSpace_l2_real : CompleteSpace (H × ℝ) := by
  letI : PseudoMetricSpace (H × ℝ) := WithLp.pseudoMetricSpaceToProd (p := 2) (α := H) (β := ℝ)
  exact (WithLp.uniformEquivProd (p := 2) H ℝ).completeSpace_iff.1 inferInstance

/-- Canonical raw-product `ℓ²` Hilbert bridge on `H × ℝ`, with inner product
`⟪(u₁, v₁), (u₂, v₂)⟫ = ⟪u₁, u₂⟫ + v₁ * v₂`. -/
noncomputable abbrev prod_innerProductSpace_l2_real : @InnerProductSpace ℝ (H × ℝ) _ (prod_seminormedAddCommGroup_l2_real (H := H)) := by
  letI : SeminormedAddCommGroup (H × ℝ) := prod_seminormedAddCommGroup_l2_real (H := H)
  letI : NormedAddCommGroup (H × ℝ) := prod_normedAddCommGroup_l2_real (H := H)
  letI : NormedSpace ℝ (H × ℝ) := prod_normedSpace_l2_real (H := H)
  exact
    { inner x y := ⟪x.1, y.1⟫_ℝ + x.2 * y.2
      norm_sq_eq_re_inner x := by
        have hnorm : @Norm.norm (H × ℝ) (prod_seminormedAddCommGroup_l2_real (H := H)).toNorm x =
            ‖WithLp.toLp 2 x‖ := by
          exact WithLp.norm_seminormedAddCommGroupToProd (p := 2) (α := H) (β := ℝ) x
        have hnorm_sq :
            @Norm.norm (H × ℝ) (prod_seminormedAddCommGroup_l2_real (H := H)).toNorm x ^ 2 =
              ‖WithLp.toLp 2 x‖ ^ 2 := by
          simpa using congrArg (fun t : ℝ ↦ t ^ 2) hnorm
        exact hnorm_sq.trans <| by
          simpa [sq] using (WithLp.prod_norm_sq_eq_of_L2 (x := WithLp.toLp 2 x))
      conj_inner_symm x y := by
        simp [real_inner_comm, mul_comm, add_comm]
      add_left x y z := by
        change ⟪x.1 + y.1, z.1⟫_ℝ + (x.2 + y.2) * z.2 =
          ⟪x.1, z.1⟫_ℝ + x.2 * z.2 + (⟪y.1, z.1⟫_ℝ + y.2 * z.2)
        rw [inner_add_left]
        ring_nf
      smul_left x y r := by
        change ⟪r • x.1, y.1⟫_ℝ + (r * x.2) * y.2 =
          r * (⟪x.1, y.1⟫_ℝ + x.2 * y.2)
        rw [inner_smul_left]
        simp
        ring_nf }

end ProductBridge

section ProductBridgeInner

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

attribute [local instance] prod_seminormedAddCommGroup_l2_real
attribute [local instance] prod_normedAddCommGroup_l2_real
attribute [local instance] prod_normedSpace_l2_real
attribute [local instance] prod_innerProductSpace_l2_real

/-- The product `ℓ²` inner product on `H × ℝ` separates into the `H`-component plus the real
product of the second coordinates. Proved by `rfl` against the canonical product bridge, since
the bridge's `Inner` field is exactly this separating form. -/
@[simp] theorem prod_inner_l2_real_apply (p q : H × ℝ) :
    ⟪p, q⟫_ℝ = ⟪p.1, q.1⟫_ℝ + p.2 * q.2 := by
  rfl

end ProductBridgeInner

end ERealFunction

namespace ERealFunction

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap08/Proposition_8_2 -/

section DomEpigraph

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- The effective domain of `f` is the first-coordinate projection of its real-height epigraph. -/
theorem dom_eq_fst_image_epigraph (f : H → EReal) :
    dom f = (LinearMap.fst ℝ H ℝ) '' epigraph f := by
  ext x
  constructor
  · intro hx
    rcases EReal.lt_iff_exists_real_btwn.mp ((mem_dom_iff f x).mp hx) with ⟨ξ, hξ, _⟩
    refine ⟨(x, ξ), ?_, rfl⟩
    rw [mem_epigraph_iff]
    exact hξ.le
  · rintro ⟨p, hp, rfl⟩
    rw [mem_dom_iff]
    exact lt_of_le_of_lt ((mem_epigraph_iff _ _ _).mp hp) (EReal.coe_lt_top p.2)

/-- The effective domain of a function with convex real-height epigraph is convex. -/
theorem convex_dom_of_convex_epigraph (f : H → EReal) (hconv : Convex ℝ (epigraph f)) :
    Convex ℝ (dom f) := by
  rw [dom_eq_fst_image_epigraph (f := f)]
  simpa using hconv.linear_image (LinearMap.fst ℝ H ℝ)

end DomEpigraph

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap13/Proposition_13_12 -/

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 13 12: a real-valued affine defect inequality rearranges in `EReal`. -/
lemma affine_defect_le_real_iff
    (f : H → EReal) (x u : H) (μ : ℝ) :
    ((((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) ≤ (μ : EReal)) ↔
      (((⟪x, u⟫_ℝ - μ : ℝ) : EReal) ≤ f x) := by
  constructor
  · intro h
    have h' : (((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ (μ : EReal) + f x) :=
      (EReal.sub_le_iff_le_add
        (a := (((⟪x, u⟫_ℝ : ℝ) : EReal)))
        (b := f x)
        (c := (μ : EReal))
        (.inr (EReal.coe_ne_top μ))
        (.inr (EReal.coe_ne_bot μ))).1 h
    have h'' : (((⟪x, u⟫_ℝ : ℝ) : EReal) - (μ : EReal) ≤ f x) :=
      EReal.sub_le_of_le_add' h'
    simpa [EReal.coe_sub] using h''
  · intro h
    have h' : (((⟪x, u⟫_ℝ : ℝ) : EReal) - (μ : EReal) ≤ f x) := by
      simpa [EReal.coe_sub] using h
    have h'' : (((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ f x + (μ : EReal)) :=
      (EReal.sub_le_iff_le_add
        (a := (((⟪x, u⟫_ℝ : ℝ) : EReal)))
        (b := (μ : EReal))
        (c := f x)
        (.inl (EReal.coe_ne_bot μ))
        (.inl (EReal.coe_ne_top μ))).1 h'
    exact EReal.sub_le_of_le_add' h''

/-- Proposition 13 12: a point `(u, μ)` lies in the epigraph of the conjugate if and only if the
continuous affine functional `x ↦ ⟪x, u⟫ - μ` is a minorant of `f`. -/
theorem mem_epigraph_conjugate_iff
    (f : H → EReal) (u : H) (μ : ℝ) :
    (u, μ) ∈ epigraph f∗ ↔
      ∀ x : H, (((⟪x, u⟫_ℝ - μ : ℝ) : EReal) ≤ f x) := by
  rw [mem_epigraph_iff, conjugate_apply]
  constructor
  · intro h x
    have hx : ((((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) ≤ (μ : EReal)) :=
      le_trans (le_iSup (fun y : H ↦ (((⟪y, u⟫_ℝ : ℝ) : EReal) - f y)) x) h
    exact (affine_defect_le_real_iff f x u μ).1 hx
  · intro h
    refine iSup_le fun x ↦ ?_
    exact (affine_defect_le_real_iff f x u μ).2 (h x)

end Conjugation

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap13/Proposition_13_16 -/

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 13 16: every affine defect appearing in the definition of the Fenchel
conjugate is bounded above by the conjugate value. -/
private theorem affine_defect_le_conjugate
    (f : H → EReal) (x u : H) :
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) ≤ f∗ u := by
  rw [conjugate_apply]
  exact le_iSup (fun y : H ↦ (((⟪y, u⟫_ℝ : ℝ) : EReal) - f y)) x

/-- Helper for Proposition 13 16: Fenchel conjugation reverses the pointwise order. -/
private theorem conjugate_antitone_local :
    Antitone (conjugate : (H → EReal) → H → EReal) := by
  intro f g hfg u
  rw [conjugate_apply, conjugate_apply]
  refine iSup_le fun x ↦ ?_
  calc
    (((⟪x, u⟫_ℝ : ℝ) : EReal) - g x)
        ≤ (((⟪x, u⟫_ℝ : ℝ) : EReal) - f x) := by
          exact EReal.sub_le_sub le_rfl (hfg x)
    _ ≤ ⨆ y : H, (((⟪y, u⟫_ℝ : ℝ) : EReal) - f y) := by
          exact le_iSup (fun y : H ↦ (((⟪y, u⟫_ℝ : ℝ) : EReal) - f y)) x

/-- Proposition 13.16 (1): every extended-real-valued function dominates its biconjugate. -/
theorem biconjugate_le (f : H → EReal) :
    f∗∗ ≤ f := by
  intro x
  by_cases htop : f x = ⊤
  · simp [htop]
  by_cases hbot : f x = ⊥
  · have hconj_top : ∀ u : H, f∗ u = ⊤ := by
      intro u
      have htop_le : (⊤ : EReal) ≤ f∗ u := by
        simpa [hbot] using affine_defect_le_conjugate (f := f) (x := x) (u := u)
      exact top_le_iff.mp htop_le
    have hxle : f∗∗ x ≤ ⊥ := by
      rw [conjugate_apply]
      refine iSup_le fun u ↦ ?_
      rw [hconj_top u]
      simp
    simpa [hbot] using hxle
  · rw [conjugate_apply]
    refine iSup_le fun u ↦ ?_
    have hdefect :
        (((⟪u, x⟫_ℝ : ℝ) : EReal) - f x) ≤ f∗ u := by
      simpa [real_inner_comm] using affine_defect_le_conjugate (f := f) (x := x) (u := u)
    have hsum :
        (((⟪u, x⟫_ℝ : ℝ) : EReal) ≤ f∗ u + f x) :=
      (EReal.sub_le_iff_le_add (Or.inl hbot) (Or.inl htop)).1 hdefect
    exact
      (EReal.sub_le_iff_le_add (Or.inr htop) (Or.inr hbot)).2
        (by simpa [add_comm] using hsum)

/-- Proposition 13.16 (3): taking biconjugates preserves the pointwise order. -/
theorem biconjugate_mono :
    Monotone (fun f : H → EReal ↦ f∗∗) := by
  intro f g hfg
  exact conjugate_antitone_local (conjugate_antitone_local hfg)

/-- Proposition 13.16 (4): the triple Fenchel conjugate of a function equals its single
conjugate. -/
theorem triple_conjugate_eq_conjugate
    (f : H → EReal) :
    f∗∗∗ = f∗ := by
  apply le_antisymm
  · exact biconjugate_le (f := f∗)
  · exact conjugate_antitone_local (biconjugate_le (f := f))

/-- Proposition 13.16 (5): applying biconjugation to the Fenchel conjugate fixes the
conjugate. -/
theorem conjugate_biconjugate_eq_self
    (f : H → EReal) :
    (f∗)∗∗ = f∗ := by
  simpa using triple_conjugate_eq_conjugate (f := f)

end Conjugation

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap13/Theorem_13_37 -/

section FenchelMoreau

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable local instance prod_seminormedAddCommGroup_l2_real_inst : SeminormedAddCommGroup (H × ℝ) :=
  prod_seminormedAddCommGroup_l2_real (H := H)

noncomputable local instance prod_normedAddCommGroup_l2_real_inst : NormedAddCommGroup (H × ℝ) :=
  prod_normedAddCommGroup_l2_real (H := H)

noncomputable local instance prod_normedSpace_l2_real_inst : NormedSpace ℝ (H × ℝ) :=
  prod_normedSpace_l2_real (H := H)

noncomputable local instance prod_completeSpace_l2_real_inst : CompleteSpace (H × ℝ) :=
  prod_completeSpace_l2_real (H := H)

noncomputable local instance prod_innerProductSpace_l2_real_inst : InnerProductSpace ℝ (H × ℝ) :=
  prod_innerProductSpace_l2_real (H := H)

/-- The `ℓ²` product inner product on `H × ℝ` splits componentwise. -/
private theorem inner_pair_eq {z w : H × ℝ} :
    ⟪z, w⟫_ℝ = ⟪z.1, w.1⟫_ℝ + z.2 * w.2 := by
  rcases z with ⟨z₁, z₂⟩
  rcases w with ⟨w₁, w₂⟩
  rfl

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 13 37: a domain point yields the canonical real-height epigraph point at
`toReal`. -/
private theorem mem_epigraph_toReal_of_mem_dom
    {f : H → EReal} (hproper : IsProper f) {x : H} (hx : x ∈ dom f) :
    (x, (f x).toReal) ∈ epigraph f := by
  have hx_top : f x ≠ ⊤ := ne_of_lt ((mem_dom_iff f x).mp hx)
  have hx_bot : f x ≠ ⊥ := hproper.1 x
  rw [mem_epigraph_iff]
  simp [EReal.coe_toReal hx_top hx_bot]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 13 37: points outside the domain are exactly the `⊤`-valued points. -/
private theorem value_eq_top_of_not_mem_dom
    {f : H → EReal} {x : H} (hx : x ∉ dom f) :
    f x = ⊤ := by
  by_contra htop
  exact hx ((mem_dom_iff_ne_top).2 htop)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 13 37: properness provides one real-height epigraph point. -/
private theorem exists_mem_epigraph_of_isProper
    {f : H → EReal} (hproper : IsProper f) :
    (epigraph f).Nonempty := by
  rcases hproper.2 with ⟨x, hx⟩
  refine ⟨(x, (f x).toReal), ?_⟩
  exact mem_epigraph_toReal_of_mem_dom hproper hx

/-- Helper for Theorem 13 37: if `x` lies in `closure (dom f)` and `ξ < f x`, then some
continuous affine minorant of `f` lies strictly above `ξ` at `x`. -/
private theorem exists_strict_affine_minorant_of_lt_of_mem_gamma_of_mem_closure_dom
    {f : H → EReal} (hproper : IsProper f) (hf : f ∈ Γ(H))
    {x : H} (hx_closure : x ∈ closure (dom f)) {ξ : ℝ} (hξ : (ξ : EReal) < f x) :
    ∃ u : H, ∃ η : ℝ,
      (∀ y : H, (((⟪y, u⟫_ℝ + η : ℝ) : EReal) ≤ f y)) ∧
        (ξ : EReal) < (((⟪x, u⟫_ℝ + η : ℝ) : EReal)) := by
  rcases (mem_gamma_iff f).mp hf with ⟨hf_conv, hf_lsc⟩
  have hEpi_conv : Convex ℝ (epigraph f) := by
    refine (convex_epigraph_iff_jensen_on_dom f).2 ?_
    intro y z hy hz a ha ha_lt_one
    exact hf_conv ha.le ha_lt_one.le
  have hEpi_closed : IsClosed (epigraph f) :=
    (lowerSemicontinuous_iff_isClosed_epigraph f).mp hf_lsc
  have hq_not_mem : (x, ξ) ∉ epigraph f := by
    intro hxξ
    exact (not_le_of_gt hξ) ((mem_epigraph_iff f x ξ).mp hxξ)
  obtain ⟨w, β, hsep, hq_out⟩ :=
    exists_closedHalfspace_separating_of_not_mem_of_isClosed_of_convex
      hEpi_closed hEpi_conv hq_not_mem
  have hw₂_nonpos : w.2 ≤ 0 := by
    by_contra hw₂_pos
    rcases exists_mem_epigraph_of_isProper hproper with ⟨⟨p, π⟩, hpπ⟩
    let t : ℝ := |β - ⟪(p, π), w⟫_ℝ| / w.2 + 1
    have ht_nonneg : 0 ≤ t := by
      have hw₂_pos' : 0 < w.2 := lt_of_not_ge hw₂_pos
      dsimp [t]
      positivity
    have hpπt : (p, π + t) ∈ epigraph f := by
      rw [mem_epigraph_iff] at hpπ ⊢
      exact le_trans hpπ <| by
        exact_mod_cast (le_add_of_nonneg_right ht_nonneg)
    have hpair_base : ⟪(p, π), w⟫_ℝ = ⟪p, w.1⟫_ℝ + π * w.2 := by
      rfl
    have hpair_shift : ⟪(p, π + t), w⟫_ℝ = ⟪(p, π), w⟫_ℝ + t * w.2 := by
      calc
        ⟪(p, π + t), w⟫_ℝ = ⟪p, w.1⟫_ℝ + (π + t) * w.2 := by
          rfl
        _ = (⟪p, w.1⟫_ℝ + π * w.2) + t * w.2 := by ring
        _ = ⟪(p, π), w⟫_ℝ + t * w.2 := by rw [hpair_base]
    have hlarge : β < ⟪(p, π + t), w⟫_ℝ := by
      have habs : |β - ⟪(p, π), w⟫_ℝ| ≤ t * w.2 := by
        dsimp [t]
        have hw₂_pos' : 0 < w.2 := lt_of_not_ge hw₂_pos
        have hmul :
            |β - ⟪(p, π), w⟫_ℝ| ≤ |β - ⟪(p, π), w⟫_ℝ| + w.2 := by
          linarith
        have hdiv :
            |β - ⟪(p, π), w⟫_ℝ| ≤
              (|β - ⟪(p, π), w⟫_ℝ| / w.2 + 1) * w.2 := by
          have hEq :
              (|β - ⟪(p, π), w⟫_ℝ| / w.2 + 1) * w.2 =
                |β - ⟪(p, π), w⟫_ℝ| + w.2 := by
            field_simp [hw₂_pos'.ne']
          simpa only [t, hEq] using hmul
        exact hdiv
      have hstrict : |β - ⟪(p, π), w⟫_ℝ| < t * w.2 := by
        dsimp [t]
        have hw₂_pos' : 0 < w.2 := lt_of_not_ge hw₂_pos
        have hplus : |β - ⟪(p, π), w⟫_ℝ| < |β - ⟪(p, π), w⟫_ℝ| + w.2 := by
          linarith
        have hEq :
            (|β - ⟪(p, π), w⟫_ℝ| / w.2 + 1) * w.2 =
              |β - ⟪(p, π), w⟫_ℝ| + w.2 := by
          field_simp [hw₂_pos'.ne']
        simpa only [t, hEq] using hplus
      linarith [hpair_shift, (abs_lt.mp hstrict).right]
    exact (not_le_of_gt hlarge) (hsep hpπt)
  have hw₂_neg : w.2 < 0 := by
    by_cases hw₂_zero : w.2 = 0
    · have hdom_half :
          dom f ⊆ {y : H | ⟪y, w.1⟫_ℝ ≤ β} := by
        intro y hy
        have hy_epi : (y, (f y).toReal) ∈ epigraph f :=
          mem_epigraph_toReal_of_mem_dom hproper hy
        have hy_sep : ⟪(y, (f y).toReal), w⟫_ℝ ≤ β := hsep hy_epi
        have hy_sep' : ⟪y, w.1⟫_ℝ + (f y).toReal * w.2 ≤ β := by
          simpa [inner_pair_eq] using hy_sep
        simpa [hw₂_zero] using hy_sep'
      have hhalf_closed : IsClosed {y : H | ⟪y, w.1⟫_ℝ ≤ β} := by
        exact isClosed_le (continuous_id.inner continuous_const) continuous_const
      have hx_half : x ∈ {y : H | ⟪y, w.1⟫_ℝ ≤ β} :=
        (closure_minimal hdom_half hhalf_closed) hx_closure
      have hq_half : (x, ξ) ∈ {z : H × ℝ | ⟪z, w⟫_ℝ ≤ β} := by
        simpa [inner_pair_eq, hw₂_zero] using hx_half
      exact False.elim (hq_out hq_half)
    · exact lt_of_le_of_ne hw₂_nonpos hw₂_zero
  let δ : ℝ := -w.2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    linarith
  let u : H := δ⁻¹ • w.1
  let η : ℝ := -β / δ
  refine ⟨u, η, ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ dom f
    · have hy_epi : (y, (f y).toReal) ∈ epigraph f :=
        mem_epigraph_toReal_of_mem_dom hproper hy
      have hy_sep : ⟪(y, (f y).toReal), w⟫_ℝ ≤ β := hsep hy_epi
      have hreal_base :
          ⟪y, w.1⟫_ℝ + (f y).toReal * w.2 ≤ β := by
        simpa [inner_pair_eq] using hy_sep
      have hreal_num :
          ⟪y, w.1⟫_ℝ - β ≤ (f y).toReal * δ := by
        dsimp [δ] at *
        linarith
      have hreal_div :
          (⟪y, w.1⟫_ℝ - β) / δ ≤ (f y).toReal := by
        exact (div_le_iff₀ hδ_pos).2 hreal_num
      have hrewrite :
          ⟪y, u⟫_ℝ + η = (⟪y, w.1⟫_ℝ - β) / δ := by
        dsimp [u, η]
        rw [real_inner_smul_right]
        field_simp [hδ_pos.ne']
        ring
      have hcast :
          (((⟪y, u⟫_ℝ + η : ℝ) : EReal) ≤ (((f y).toReal : ℝ) : EReal)) := by
        rw [hrewrite]
        exact_mod_cast hreal_div
      have hy_top : f y ≠ ⊤ := ne_of_lt ((mem_dom_iff f y).mp hy)
      have hy_bot : f y ≠ ⊥ := hproper.1 y
      simpa [EReal.coe_toReal hy_top hy_bot] using hcast
    · rw [value_eq_top_of_not_mem_dom hy]
      exact le_top
  · have hq_real : β < ⟪(x, ξ), w⟫_ℝ := by
      exact lt_of_not_ge hq_out
    have hq_real' : β < ⟪x, w.1⟫_ℝ + ξ * w.2 := by
      simpa [inner_pair_eq] using hq_real
    have hnum : β + ξ * δ < ⟪x, w.1⟫_ℝ := by
      dsimp [δ] at *
      simpa using hq_real'
    have hdiv : ξ < (⟪x, w.1⟫_ℝ - β) / δ := by
      refine (lt_div_iff₀ hδ_pos).2 ?_
      linarith
    have hrewrite :
        ⟪x, u⟫_ℝ + η = (⟪x, w.1⟫_ℝ - β) / δ := by
      dsimp [u, η]
      rw [real_inner_smul_right]
      field_simp [hδ_pos.ne']
      ring
    exact_mod_cast (hrewrite ▸ hdiv)

/-- Helper for Theorem 13 37: proper `Γ(H)` functions admit a global continuous affine minorant in
the canonical textbook form `y ↦ ⟪y,u⟫ + η`. -/
private theorem exists_global_affine_minorant_of_isProper_of_mem_gamma
    {f : H → EReal} (hproper : IsProper f) (hf : f ∈ Γ(H)) :
    ∃ u : H, ∃ η : ℝ, ∀ y : H, (((⟪y, u⟫_ℝ + η : ℝ) : EReal) ≤ f y) := by
  rcases hproper.2 with ⟨x, hx⟩
  have hx_top : f x ≠ ⊤ := ne_of_lt ((mem_dom_iff f x).mp hx)
  have hx_bot : f x ≠ ⊥ := hproper.1 x
  let ξ : ℝ := (f x).toReal - 1
  have hξ : (ξ : EReal) < f x := by
    have hreal : ξ < (f x).toReal := by
      dsimp [ξ]
      linarith
    have hcast : ((ξ : ℝ) : EReal) < (((f x).toReal : ℝ) : EReal) := by
      exact_mod_cast hreal
    simpa [EReal.coe_toReal hx_top hx_bot] using hcast
  rcases exists_strict_affine_minorant_of_lt_of_mem_gamma_of_mem_closure_dom
      hproper hf (subset_closure hx) hξ with ⟨u, η, hminor, _⟩
  exact ⟨u, η, hminor⟩

/-- Helper for Theorem 13 37: a canonical affine minorant strictly above `ξ` at `x` forces the
Fenchel biconjugate value at `x` to dominate `ξ`. -/
private theorem strict_lower_bound_le_biconjugate_of_affine_minorant
    {f : H → EReal} {x u : H} {η ξ : ℝ}
    (hminor : ∀ y : H, (((⟪y, u⟫_ℝ + η : ℝ) : EReal) ≤ f y))
    (hξ : (ξ : EReal) < (((⟪x, u⟫_ℝ + η : ℝ) : EReal))) :
    (ξ : EReal) ≤ f∗∗ x := by
  have hmem : (u, -η) ∈ epigraph f∗ := by
    refine (mem_epigraph_conjugate_iff f u (-η)).2 ?_
    intro y
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hminor y
  have hconj : f∗ u ≤ ((-η : ℝ) : EReal) := (mem_epigraph_iff _ _ _).mp hmem
  have hneg : ((η : ℝ) : EReal) ≤ -f∗ u := by
    rw [← EReal.neg_le_neg_iff]
    simpa using hconj
  have haffine_le :
      (((⟪x, u⟫_ℝ + η : ℝ) : EReal) ≤ (((⟪x, u⟫_ℝ : ℝ) : EReal) - f∗ u)) := by
    calc
      (((⟪x, u⟫_ℝ + η : ℝ) : EReal))
          = (((⟪x, u⟫_ℝ : ℝ) : EReal) + ((η : ℝ) : EReal)) := by
              rw [EReal.coe_add]
      _ ≤ (((⟪x, u⟫_ℝ : ℝ) : EReal) + -f∗ u) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hneg (((⟪x, u⟫_ℝ : ℝ) : EReal))
      _ = (((⟪x, u⟫_ℝ : ℝ) : EReal) - f∗ u) := by
        rfl
  have hdefect_le : (((⟪x, u⟫_ℝ : ℝ) : EReal) - f∗ u) ≤ f∗∗ x := by
    simpa [conjugate_apply, real_inner_comm] using
      (le_iSup (fun y : H ↦ (((⟪y, x⟫_ℝ : ℝ) : EReal) - f∗ y)) u)
  exact hξ.le.trans (haffine_le.trans hdefect_le)

/-- Helper for Theorem 13 37: outside `closure (dom f)`, the Fenchel biconjugate of a proper
member of `Γ(H)` is identically `⊤`. -/
private theorem biconjugate_eq_top_of_not_mem_closure_dom_of_mem_gamma
    {f : H → EReal} (hproper : IsProper f) (hf : f ∈ Γ(H))
    {x : H} (hx : x ∉ closure (dom f)) :
    f∗∗ x = ⊤ := by
  rcases (mem_gamma_iff f).mp hf with ⟨hf_conv, _⟩
  have hEpi_conv : Convex ℝ (epigraph f) := by
    refine (convex_epigraph_iff_jensen_on_dom f).2 ?_
    intro y z hy hz a ha ha_lt_one
    exact hf_conv ha.le ha_lt_one.le
  have hdom_conv : Convex ℝ (dom f) := convex_dom_of_convex_epigraph f hEpi_conv
  obtain ⟨u₀, β₀, hdom_half, hx_out⟩ :=
    exists_closedHalfspace_separating_of_not_mem_of_isClosed_of_convex
      isClosed_closure hdom_conv.closure hx
  rcases exists_global_affine_minorant_of_isProper_of_mem_gamma hproper hf with ⟨v, η, hminor⟩
  have hgap : β₀ < ⟪x, u₀⟫_ℝ := by
    exact lt_of_not_ge hx_out
  refine (EReal.eq_top_iff_forall_lt _).2 ?_
  intro M
  let t : ℝ := |M - (⟪x, v⟫_ℝ + η)| / (⟪x, u₀⟫_ℝ - β₀) + 1
  have hgap_pos : 0 < ⟪x, u₀⟫_ℝ - β₀ := by
    linarith
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  let w : H := v + t • u₀
  have hw_conj :
      f∗ w ≤ ((t * β₀ - η : ℝ) : EReal) := by
    rw [conjugate_apply]
    refine iSup_le ?_
    intro y
    by_cases hy : y ∈ dom f
    · have hy_top : f y ≠ ⊤ := ne_of_lt ((mem_dom_iff f y).mp hy)
      have hy_bot : f y ≠ ⊥ := hproper.1 y
      have hy_half : ⟪y, u₀⟫_ℝ ≤ β₀ := by
        exact hdom_half (subset_closure hy)
      have hminor_real :
          ⟪y, v⟫_ℝ + η ≤ (f y).toReal := by
        have hcast : (((⟪y, v⟫_ℝ + η : ℝ) : EReal) ≤ (((f y).toReal : ℝ) : EReal)) := by
          exact le_trans (hminor y) (by
            simp [EReal.coe_toReal hy_top hy_bot])
        exact_mod_cast hcast
      have hlinear :
          ⟪y, w⟫_ℝ - (f y).toReal ≤ t * β₀ - η := by
        dsimp [w]
        rw [inner_add_right, real_inner_smul_right]
        have htbeta : t * ⟪y, u₀⟫_ℝ ≤ t * β₀ := by
          exact mul_le_mul_of_nonneg_left hy_half ht_pos.le
        linarith
      have hcast :
          (((⟪y, w⟫_ℝ : ℝ) : EReal) - (((f y).toReal : ℝ) : EReal)) ≤
            ((t * β₀ - η : ℝ) : EReal) := by
        rw [← EReal.coe_sub]
        exact_mod_cast hlinear
      simpa [EReal.coe_toReal hy_top hy_bot] using hcast
    · rw [value_eq_top_of_not_mem_dom hy]
      simp
  have hbase_lt :
      (M : EReal) < (((⟪x, w⟫_ℝ : ℝ) : EReal) - ((t * β₀ - η : ℝ) : EReal)) := by
    have hreal : M < ⟪x, w⟫_ℝ - (t * β₀ - η) := by
      dsimp [w, t]
      rw [inner_add_right, real_inner_smul_right]
      have habs : |M - (⟪x, v⟫_ℝ + η)| < |M - (⟪x, v⟫_ℝ + η)| + (⟪x, u₀⟫_ℝ - β₀) := by
        linarith
      have hEq :
          (|M - (⟪x, v⟫_ℝ + η)| / (⟪x, u₀⟫_ℝ - β₀) + 1) *
              (⟪x, u₀⟫_ℝ - β₀) =
            |M - (⟪x, v⟫_ℝ + η)| + (⟪x, u₀⟫_ℝ - β₀) := by
        field_simp [hgap_pos.ne']
      have hboost :
          |M - (⟪x, v⟫_ℝ + η)| <
            t * (⟪x, u₀⟫_ℝ - β₀) := by
        simpa [t, hEq] using habs
      have hdiff : M - (⟪x, v⟫_ℝ + η) < t * (⟪x, u₀⟫_ℝ - β₀) := by
        exact (abs_lt.mp hboost).2
      linarith
    rw [← EReal.coe_sub]
    exact_mod_cast hreal
  have hterm_le : (((⟪x, w⟫_ℝ : ℝ) : EReal) - ((t * β₀ - η : ℝ) : EReal)) ≤ f∗∗ x := by
    have hdefect : (((⟪x, w⟫_ℝ : ℝ) : EReal) - f∗ w) ≤ f∗∗ x := by
      simpa [conjugate_apply, real_inner_comm] using
        (le_iSup (fun y : H ↦ (((⟪y, x⟫_ℝ : ℝ) : EReal) - f∗ y)) w)
    have hsub :
        (((⟪x, w⟫_ℝ : ℝ) : EReal) - ((t * β₀ - η : ℝ) : EReal)) ≤
          (((⟪x, w⟫_ℝ : ℝ) : EReal) - f∗ w) := by
      exact EReal.sub_le_sub le_rfl hw_conj
    exact le_trans hsub hdefect
  exact lt_of_lt_of_le hbase_lt hterm_le

/-- Helper for Theorem 13 37: every proper member of `Γ(H)` is bounded above by its Fenchel
biconjugate. -/
private theorem le_biconjugate_of_isProper_of_mem_gamma
    {f : H → EReal} (hproper : IsProper f) (hf : f ∈ Γ(H)) :
    f ≤ f∗∗ := by
  intro x
  by_cases hx_closure : x ∈ closure (dom f)
  · refine le_of_forall_lt fun ξ hξ ↦ ?_
    rcases EReal.lt_iff_exists_real_btwn.mp hξ with ⟨ξ₀, hξ_lt, hξ₀_lt⟩
    rcases exists_strict_affine_minorant_of_lt_of_mem_gamma_of_mem_closure_dom
        hproper hf hx_closure hξ₀_lt with ⟨u, η, hminor, hstrict⟩
    exact lt_of_lt_of_le hξ_lt
      (strict_lower_bound_le_biconjugate_of_affine_minorant hminor hstrict)
  · have hx_top : f x = ⊤ := by
      by_contra hx_top
      have hx_dom : x ∈ dom f := (mem_dom_iff_ne_top).2 hx_top
      exact hx_closure (subset_closure hx_dom)
    rw [hx_top]
    rw [biconjugate_eq_top_of_not_mem_closure_dom_of_mem_gamma hproper hf hx_closure]

omit [CompleteSpace H] in
/-- Helper for Theorem 13 37: a global affine minorant furnishes a finite conjugate value, hence a
domain point of the conjugate. -/
private theorem mem_dom_conjugate_of_affine_minorant
    {f : H → EReal} {u : H} {η : ℝ}
    (hminor : ∀ y : H, (((⟪y, u⟫_ℝ + η : ℝ) : EReal) ≤ f y)) :
    u ∈ dom f∗ := by
  have hmem : (u, -η) ∈ epigraph f∗ := by
    refine (mem_epigraph_conjugate_iff f u (-η)).2 ?_
    intro y
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hminor y
  have hu_lt_top : f∗ u < ⊤ := by
    exact lt_of_le_of_lt ((mem_epigraph_iff _ _ _).mp hmem) (EReal.coe_lt_top (-η))
  exact (mem_dom_iff (f∗) u).2 hu_lt_top

/-- Theorem 13 37: for a proper extended-real-valued function on a real Hilbert space, being lower
semicontinuous and convex, equivalently belonging to `Γ(H)`, is equivalent to coinciding with its
Fenchel biconjugate. -/
theorem mem_gamma_iff_eq_biconjugate_of_is_proper
    {f : H → EReal} (hproper : IsProper f) :
    f ∈ Γ(H) ↔ f∗∗ = f := by
  constructor
  · intro hf
    apply le_antisymm
    · exact biconjugate_le f
    · exact le_biconjugate_of_isProper_of_mem_gamma hproper hf
  · intro hEq
    rw [← hEq]
    exact conjugate_mem_gamma (f := f∗)

/-- If a proper extended-real-valued function on a real Hilbert space is lower semicontinuous and
convex, equivalently lies in `Γ(H)`, then its Fenchel conjugate is proper. -/
theorem conjugate_is_proper_of_mem_gamma
    {f : H → EReal} (hproper : IsProper f) (hf : f ∈ Γ(H)) :
    IsProper f∗ := by
  rcases exists_global_affine_minorant_of_isProper_of_mem_gamma hproper hf with ⟨u, η, hminor⟩
  refine ⟨fun v ↦ conjugate_ne_bot_of_isProper hproper v, ?_⟩
  exact ⟨u, mem_dom_conjugate_of_affine_minorant hminor⟩

end FenchelMoreau

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap13/Corollary_13_38 -/

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Corollary 13 38: the Fenchel conjugate of an `]-∞,+∞]`-valued function with
nonempty effective domain never takes the value `-∞`. -/
theorem conjugate_ne_bot_of_effectiveDomain_nonempty
    {f : H → Set.Ioi (⊥ : EReal)} (hdom : (effectiveDomain f).Nonempty) (u : H) :
    f.asEReal∗ u ≠ ⊥ := by
  have hproper : IsProper f.asEReal := by
    refine ⟨fun x ↦ ne_of_gt (f x).2, ?_⟩
    simpa [effectiveDomain, dom] using hdom
  exact conjugate_ne_bot_of_isProper hproper u

/-- Helper for Corollary 13 38: every `Γ₀(H)` function has Fenchel conjugate with nonempty
domain. -/
theorem dom_conjugate_nonempty_of_mem_gammaZero
    [CompleteSpace H] {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    (dom f.asEReal∗).Nonempty := by
  have hproper_f : IsProper f.asEReal := isProper_of_mem_gammaZero hf
  have hgamma_f : f.asEReal ∈ gamma H := asEReal_mem_gamma_of_mem_gammaZero hf
  exact (conjugate_is_proper_of_mem_gamma hproper_f hgamma_f).2

/-- The Fenchel conjugate of an `]-∞,+∞]`-valued function with nonempty effective domain, packaged
again as `]-∞,+∞]`-valued. -/
noncomputable abbrev properConjugateIoi (f : H → Set.Ioi (⊥ : EReal))
    (hdom : (effectiveDomain f).Nonempty) :
    H → Set.Ioi (⊥ : EReal) :=
  fun u ↦
    ⟨f.asEReal∗ u,
      bot_lt_iff_ne_bot.mpr (conjugate_ne_bot_of_effectiveDomain_nonempty hdom u)⟩

/-- Coercing `properConjugateIoi f hdom` back to `EReal` recovers the canonical Fenchel
conjugate `f.asEReal∗`. -/
@[simp] theorem properConjugateIoi_apply
    (f : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain f).Nonempty) (u : H) :
    (properConjugateIoi f hdom u : EReal) = f.asEReal∗ u :=
  rfl

/-- The `Γ₀(H)` specialization of `properConjugateIoi`. -/
noncomputable abbrev gammaZeroConjugate (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    H → Set.Ioi (⊥ : EReal) :=
  properConjugateIoi f hf.2.nonempty

/- Lean cannot infer the `Γ₀(H)` witness from `f` alone, so the packaged source-facing conjugate
keeps that witness explicit and writes the canonical `Γ₀(H)` Fenchel conjugate as `f∗[hf]`. -/
scoped notation:max f "∗[" hf "]" => gammaZeroConjugate f hf

/-- Coercing `gammaZeroConjugate f hf` back to `EReal` recovers the canonical Fenchel conjugate
`f.asEReal∗`. -/
@[simp] theorem gammaZeroConjugate_apply
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    (f∗[hf] u : EReal) = f.asEReal∗ u :=
  rfl

/-- The Fenchel conjugate of a `Γ₀(H)` function again belongs to `Γ₀(H)`. -/
theorem gammaZeroConjugate_mem_gammaZero
    [CompleteSpace H] {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    f∗[hf] ∈ Γ₀(H) := by
  have hproper_conj : IsProper f.asEReal∗ := by
    refine ⟨conjugate_ne_bot_of_effectiveDomain_nonempty hf.2.nonempty,
      dom_conjugate_nonempty_of_mem_gammaZero hf⟩
  have hgamma_conj : f.asEReal∗ ∈ gamma H := conjugate_mem_gamma f.asEReal
  have hrepr : f∗[hf] = properIoi (f.asEReal∗) hproper_conj := by
    funext u
    apply Subtype.ext
    rfl
  rw [hrepr]
  exact properIoi_mem_gammaZero_of_mem_gamma hproper_conj hgamma_conj

end Conjugation

section FenchelMoreau

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Corollary 13 38: a `Γ₀(H)` function agrees with the Fenchel biconjugate of its
canonical `EReal`-valued coercion. -/
theorem biconjugate_eq_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    f.asEReal∗∗ = f.asEReal := by
  have hproper_f : IsProper f.asEReal := isProper_of_mem_gammaZero hf
  have hgamma_f : f.asEReal ∈ gamma H := asEReal_mem_gamma_of_mem_gammaZero hf
  exact (mem_gamma_iff_eq_biconjugate_of_is_proper hproper_f).mp hgamma_f

/-- Corollary 13 38: if `f ∈ Γ₀(H)`, then its canonical `Γ₀(H)`-valued Fenchel conjugate again
belongs to `Γ₀(H)`, and the Fenchel biconjugate of the `EReal`-valued coercion of `f` is `f`
itself. -/
theorem conjugate_mem_gammaZero_and_biconjugate_eq
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    f∗[hf] ∈ Γ₀(H) ∧ f.asEReal∗∗ = f.asEReal := by
  exact ⟨gammaZeroConjugate_mem_gammaZero hf, biconjugate_eq_of_mem_gammaZero hf⟩

end FenchelMoreau

section ProximityOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Corollary 13 38: a source-facing owner for the proximity operator of a
`Γ₀(H)`-valued function. -/
noncomputable def gammaZero_proximity_operator
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) : H → H :=
  proximityOperator f (hasUniqueProxPoint_of_mem_gammaZero (f := f) hf)

/-- Helper for Corollary 13 38: a source-facing owner for the scaled proximity operator of a
`Γ₀(H)`-valued function. -/
noncomputable def scaled_gammaZero_proximity_operator
    (γ : PosReal) (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) : H → H :=
  scaledProximityOperator f hf γ

/- Source-facing notation for the proximity operator of the Fenchel conjugate `f*`,
represented by the canonical `Γ₀(H)`-valued owner `f∗[hf]`. -/
notation "Prox⋆[" f ", " hf "]" =>
  gammaZero_proximity_operator (f∗[hf]) (gammaZeroConjugate_mem_gammaZero hf)

/- Source-facing notation for the scaled proximity operator `Prox_{γ f*}`,
represented by the canonical `Γ₀(H)`-valued owner `f∗[hf]`. -/
notation "Prox⋆[" γ ", " f ", " hf "]" =>
  scaled_gammaZero_proximity_operator γ (f∗[hf]) (gammaZeroConjugate_mem_gammaZero hf)

end ProximityOperator


end ERealFunction


namespace ERealFunction

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap13/Example_13_6 -/

section HalfSquaredNormConjugate

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Example 13.6: the Fenchel conjugate of the quadratic function `x ↦ ‖x‖² / 2` is itself. -/
theorem conjugate_halfSquaredNorm :
    ((halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal)∗ =
      (halfSquaredNorm : H → Set.Ioi (⊥ : EReal)).asEReal := by
  funext u
  rw [conjugate_apply]
  simp only [Function.asEReal_apply, halfSquaredNorm_apply]
  apply le_antisymm
  · refine iSup_le ?_
    intro x
    have hyoung : ⟪x, u⟫_ℝ - ‖x‖ ^ 2 / 2 ≤ ‖u‖ ^ 2 / 2 := by
      have hsq : 0 ≤ ‖x - u‖ ^ 2 := sq_nonneg _
      rw [norm_sub_sq_real] at hsq
      nlinarith
    exact_mod_cast hyoung
  · have hatt : ((⟪u, u⟫_ℝ : ℝ) : EReal) - (((‖u‖ ^ 2) / 2 : ℝ) : EReal) =
        (((‖u‖ ^ 2) / 2 : ℝ) : EReal) := by
      rw [real_inner_self_eq_norm_sq, ← EReal.coe_sub]
      congr 1
      ring
    rw [← hatt]
    exact le_iSup (fun x : H ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal) - (((‖x‖ ^ 2) / 2 : ℝ) : EReal)) u

end HalfSquaredNormConjugate

end ERealFunction

