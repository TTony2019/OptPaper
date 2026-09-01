import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.Topology.Metrizable.Basic
import Foundation.Topology.Sequences

/-!
# Hilbert WeakTopology

Weak topology on Hilbert spaces, weak closed balls, weak compactness, and bounded weakly closed criteria.
-/

open scoped InnerProductSpace
open TopologicalSpace
open scoped InnerProductSpace Pointwise
open Filter TopologicalSpace
open scoped InnerProductSpace Topology
open scoped Pointwise
open Filter

/-! Source item: Chap02/Text_2_0_8 -/
universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The level set of a real linear functional at the scalar `η`. -/
def hyperplane (f : H →ₗ[ℝ] ℝ) (η : ℝ) : Set H :=
  {x | f x = η}

/-- Text 2.0.8: a hyperplane in a real Hilbert space is a level set of a nonzero real linear
functional. -/
def is_hyperplane (s : Set H) : Prop :=
  ∃ f : H →ₗ[ℝ] ℝ, f ≠ 0 ∧ ∃ η : ℝ, s = hyperplane f η

-- Proof sketch: unfold `hyperplane`; membership is definitionally the equation `f x = η`.
/-- Membership in `hyperplane f η` is the defining linear-functional equation. -/
theorem mem_hyperplane_iff {f : H →ₗ[ℝ] ℝ} {η : ℝ} {x : H} :
    x ∈ hyperplane f η ↔ f x = η :=
  Iff.rfl

-- Proof sketch: use `f` and `η` as the witnesses in the defining existential statement for
-- `is_hyperplane`.
/-- The level set of a nonzero real linear functional is a hyperplane. -/
theorem hyperplane_is_hyperplane (f : H →ₗ[ℝ] ℝ) (hf : f ≠ 0) (η : ℝ) :
    is_hyperplane (hyperplane f η) :=
  ⟨f, hf, η, rfl⟩

-- Proof sketch: use `f` and `η` as the witnesses in the defining existential statement for
-- `is_hyperplane`.
/-- The level set of a nonzero real linear functional is a hyperplane. -/
theorem is_hyperplane_setOf_eq (f : H →ₗ[ℝ] ℝ) (hf : f ≠ 0) (η : ℝ) :
    is_hyperplane {x | f x = η} := by
  simpa [hyperplane] using hyperplane_is_hyperplane f hf η

/-! Source item: Chap02/Text_2_0_9 -/


variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The level set of the real inner-product functional `x ↦ ⟪x, u⟫_ℝ` at `η`. -/
def innerProductLevelSet (u : H) (η : ℝ) : Set H :=
  hyperplane (innerSLFlip ℝ u).toLinearMap η

/-- The closed sublevel set of the real inner-product functional `x ↦ ⟪x, u⟫_ℝ` at `η`. -/
def innerProductClosedSublevelSet (u : H) (η : ℝ) : Set H :=
  (innerSLFlip ℝ u) ⁻¹' Set.Iic η

/-- The open strict sublevel set of the real inner-product functional `x ↦ ⟪x, u⟫_ℝ` at `η`. -/
def innerProductOpenSublevelSet (u : H) (η : ℝ) : Set H :=
  (innerSLFlip ℝ u) ⁻¹' Set.Iio η

/-- The inner-product level set is the hyperplane cut out by the real linear functional
`x ↦ ⟪x, u⟫_ℝ`. -/
theorem innerProductLevelSet_eq_hyperplane (u : H) (η : ℝ) :
    innerProductLevelSet u η = hyperplane (innerSLFlip ℝ u).toLinearMap η :=
  rfl

-- Proof sketch: unfold `innerProductLevelSet`; membership is definitionally the equality
-- `inner ℝ x u = η`.
/-- Membership in the inner-product level set is the defining inner-product equation. -/
theorem mem_innerProductLevelSet_iff {u x : H} {η : ℝ} :
    x ∈ innerProductLevelSet u η ↔ ⟪x, u⟫_ℝ = η := by
  rw [innerProductLevelSet, mem_hyperplane_iff]
  change (innerSLFlip ℝ u) x = η ↔ _
  rw [innerSLFlip_apply_apply]

-- Proof sketch: unfold `innerProductClosedSublevelSet`; membership is definitionally the
-- inequality `inner ℝ x u ≤ η`.
/-- Membership in the closed inner-product sublevel set is the defining inequality. -/
theorem mem_innerProductClosedSublevelSet_iff {u x : H} {η : ℝ} :
    x ∈ innerProductClosedSublevelSet u η ↔ ⟪x, u⟫_ℝ ≤ η := by
  rw [innerProductClosedSublevelSet]
  change (innerSLFlip ℝ u) x ≤ η ↔ _
  rw [innerSLFlip_apply_apply]

-- Proof sketch: unfold `innerProductOpenSublevelSet`; membership is definitionally the strict
-- inequality `inner ℝ x u < η`.
/-- Membership in the open inner-product strict sublevel set is the defining inequality. -/
theorem mem_innerProductOpenSublevelSet_iff {u x : H} {η : ℝ} :
    x ∈ innerProductOpenSublevelSet u η ↔ ⟪x, u⟫_ℝ < η := by
  rw [innerProductOpenSublevelSet]
  change (innerSLFlip ℝ u) x < η ↔ _
  rw [innerSLFlip_apply_apply]

/-- Text 2.0.9: if `u ≠ 0`, the closed hyperplane with normal `u` and offset `η` is the level set
of `x ↦ ⟪x, u⟫_ℝ` at `η`. -/
theorem closedHyperplane_eq_setOf (u : H) (η : ℝ) (_hu : u ≠ 0) :
    innerProductLevelSet u η = {x | ⟪x, u⟫_ℝ = η} := by
  ext x
  simp [mem_innerProductLevelSet_iff]

/-- Text 2.0.9: if `u ≠ 0`, the closed half-space with outer normal `u` and offset `η` is the
sublevel set of `x ↦ ⟪x, u⟫_ℝ` at `η`. -/
theorem closedHalfSpace_eq_setOf (u : H) (η : ℝ) (_hu : u ≠ 0) :
    innerProductClosedSublevelSet u η = {x | ⟪x, u⟫_ℝ ≤ η} := by
  ext x
  simp [mem_innerProductClosedSublevelSet_iff]

/-- Text 2.0.9: if `u ≠ 0`, the open half-space with outer normal `u` and offset `η` is the
strict sublevel set of `x ↦ ⟪x, u⟫_ℝ` at `η`. -/
theorem openHalfSpace_eq_setOf (u : H) (η : ℝ) (_hu : u ≠ 0) :
    innerProductOpenSublevelSet u η = {x | ⟪x, u⟫_ℝ < η} := by
  ext x
  simp [mem_innerProductOpenSublevelSet_iff]

/-! Source item: Chap02/Text_2_0_10 -/


variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Text 2.0.10: subtracting the normal correction sends `x` onto the closed
hyperplane with normal `u` and offset `η`. -/
private lemma orthogonal_foot_mem_closedHyperplane (x u : H) (η : ℝ) (hu : u ≠ 0) :
    x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u ∈ innerProductLevelSet u η := by
  have hu_norm : ‖u‖ ≠ 0 := by
    simpa using hu
  have hu_sq : ‖u‖ ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_ne_zero hu_norm hu_norm
  -- Rewrite membership as the defining inner-product equation of the hyperplane.
  rw [mem_innerProductLevelSet_iff]
  -- Compute the inner product of the corrected point with the normal vector.
  calc
    ⟪x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u, u⟫_ℝ
        = ⟪x, u⟫_ℝ - (((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) * ⟪u, u⟫_ℝ) := by
            rw [inner_sub_left, real_inner_smul_left]
    _ = ⟪x, u⟫_ℝ - (((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) * (‖u‖ ^ 2)) := by
            rw [real_inner_self_eq_norm_sq]
    _ = ⟪x, u⟫_ℝ - (⟪x, u⟫_ℝ - η) := by
            field_simp [hu_sq]
    _ = η := by
            ring

/-- Helper for Text 2.0.10: the distance from `x` to its orthogonal foot on
`innerProductLevelSet u η` is the normalized absolute inner-product defect. -/
private lemma dist_to_orthogonal_foot_eq_abs_inner_sub_div_norm (x u : H) (η : ℝ) (hu : u ≠ 0) :
    dist x (x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u) = |⟪x, u⟫_ℝ - η| / ‖u‖ := by
  have hu_norm : ‖u‖ ≠ 0 := by
    simpa using hu
  -- Collapse the distance to the norm of the normal correction vector.
  calc
    dist x (x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u)
        = ‖((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u‖ := by
            rw [dist_eq_norm]
            simp
    _ = |(⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2| * ‖u‖ := by
            rw [norm_smul, Real.norm_eq_abs]
    _ = (|⟪x, u⟫_ℝ - η| / (‖u‖ ^ 2)) * ‖u‖ := by
            rw [abs_div, abs_of_nonneg (sq_nonneg ‖u‖)]
    _ = |⟪x, u⟫_ℝ - η| / ‖u‖ := by
            field_simp [pow_two, hu_norm]

/-- Helper for Text 2.0.10: every point of `innerProductLevelSet u η` is at least the normalized
inner-product defect away from `x`. -/
private lemma abs_inner_sub_div_norm_le_dist_of_mem_closedHyperplane
    (x y u : H) (η : ℝ) (hu : u ≠ 0) (hy : y ∈ innerProductLevelSet u η) :
    |⟪x, u⟫_ℝ - η| / ‖u‖ ≤ dist x y := by
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hy_eq : ⟪y, u⟫_ℝ = η := mem_innerProductLevelSet_iff.mp hy
  have hinner : ⟪x, u⟫_ℝ - η = ⟪x - y, u⟫_ℝ := by
    calc
      ⟪x, u⟫_ℝ - η = ⟪x, u⟫_ℝ - ⟪y, u⟫_ℝ := by
        rw [hy_eq]
      _ = ⟪x - y, u⟫_ℝ := by
        rw [inner_sub_left]
  have hcs : |⟪x - y, u⟫_ℝ| ≤ ‖x - y‖ * ‖u‖ := abs_real_inner_le_norm (x - y) u
  have hdiv : |⟪x - y, u⟫_ℝ| / ‖u‖ ≤ ‖x - y‖ := by
    exact (div_le_iff₀ hu_pos).2 (by simpa [mul_comm] using hcs)
  -- Replace the inner-product defect by the hyperplane equation and identify distance with a norm.
  simpa [hinner, dist_eq_norm] using hdiv

/-- Text 2.0.10: the distance from a point to the closed hyperplane `innerProductLevelSet u η` is
the absolute value of the inner-product defect `⟪x, u⟫_ℝ - η`, normalized by `‖u‖`. -/
-- Proof sketch: project `x` onto the hyperplane along the normal direction `u`, namely at
-- `x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u`, to get the upper bound, and use Cauchy-Schwarz on
-- `⟪x - y, u⟫_ℝ = ⟪x, u⟫_ℝ - η` for arbitrary `y ∈ innerProductLevelSet u η` to get the lower
-- bound.
theorem infDist_hyperplane_eq_abs_inner_sub_div_norm (x u : H) (η : ℝ) (hu : u ≠ 0) :
    Metric.infDist x (innerProductLevelSet u η) = |⟪x, u⟫_ℝ - η| / ‖u‖ := by
  let p := x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u
  have hp : p ∈ innerProductLevelSet u η := by
    -- The textbook witness is exactly the orthogonal foot onto the affine hyperplane.
    simpa [p] using orthogonal_foot_mem_closedHyperplane x u η hu
  have hs : (innerProductLevelSet u η).Nonempty := ⟨p, hp⟩
  have hupper : Metric.infDist x (innerProductLevelSet u η) ≤ |⟪x, u⟫_ℝ - η| / ‖u‖ := by
    -- The explicit projection witness gives the required upper bound.
    calc
      Metric.infDist x (innerProductLevelSet u η) ≤ dist x p := Metric.infDist_le_dist_of_mem hp
      _ = |⟪x, u⟫_ℝ - η| / ‖u‖ := by
        simpa [p] using dist_to_orthogonal_foot_eq_abs_inner_sub_div_norm x u η hu
  have hlower : |⟪x, u⟫_ℝ - η| / ‖u‖ ≤ Metric.infDist x (innerProductLevelSet u η) := by
    -- Every point of the hyperplane satisfies the Cauchy-Schwarz lower bound.
    rw [Metric.le_infDist hs]
    intro y hy
    exact abs_inner_sub_div_norm_le_dist_of_mem_closedHyperplane x y u η hu hy
  exact le_antisymm hupper hlower

/-! Source item: Chap02/Text_2_0_11 -/

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗]

/-- Text 2.0.11: the strong (norm) topology on a normed space is the topology induced by the
canonical metric `d x y = ‖x - y‖`. -/
theorem strong_topology_eq_metric_topology :
    (inferInstance : TopologicalSpace 𝓗) =
      (inferInstance : MetricSpace 𝓗).toUniformSpace.toTopologicalSpace := rfl

/-! Source item: Chap02/Lemma_2_22 -/
universe v w

/-- Lemma 2.22: the real-linear specialization of the uniform boundedness principle for a
pointwise bounded family of bounded operators from a Banach space into a normed space. -/
-- This is the textbook real-linear form of mathlib's canonical theorem `banach_steinhaus`.
theorem uniform_boundedness_principle {ι : Type u} {𝓧 : Type v} {𝓨 : Type w}
    [NormedAddCommGroup 𝓧] [NormedSpace ℝ 𝓧] [CompleteSpace 𝓧]
    [NormedAddCommGroup 𝓨] [NormedSpace ℝ 𝓨] {T : ι → 𝓧 →L[ℝ] 𝓨}
    (hT : ∀ x : 𝓧, ∃ C : ℝ, ∀ i : ι, ‖T i x‖ ≤ C) :
    ∃ C : ℝ, ∀ i : ι, ‖T i‖ ≤ C := by
  simpa using banach_steinhaus hT

/-! Source item: Chap02/Fact_2_33 -/


noncomputable section

/-- Helper for Fact 2.33: on a finite-dimensional real Hilbert space, the canonical map from the
weak topology back to the norm topology is continuous. -/
-- We follow the finite-coordinate route from the source proof: choose a basis, show every
-- coordinate functional is weakly continuous, and then reconstruct vectors by the inverse
-- coordinate map.
private lemma weak_symm_continuous_of_finiteDimensional
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [FiniteDimensional ℝ H] :
    Continuous ((toWeakSpace ℝ H).symm : WeakSpace ℝ H → H) := by
  let b := Module.Basis.ofVectorSpace ℝ H
  -- Each basis coordinate is a continuous linear functional, hence weakly continuous.
  have hcoords : Continuous fun x : WeakSpace ℝ H ↦ b.equivFun ((toWeakSpace ℝ H).symm x) := by
    rw [continuous_pi_iff]
    intro i
    let l : StrongDual ℝ H :=
      ⟨b.coord i, (b.coord i).continuous_of_finiteDimensional⟩
    simpa [Module.Basis.equivFun_apply, l] using
      (WeakBilin.eval_continuous ((topDualPairing ℝ H).flip) l)
  -- The inverse coordinate map on the finite product is continuous.
  have hsymm : Continuous b.equivFun.symm := b.equivFunL.symm.continuous
  -- Composing the weakly continuous coordinate map with the inverse basis map recovers the
  -- identity from `WeakSpace ℝ H` to `H`.
  have hcomp :
      (fun x : WeakSpace ℝ H ↦ b.equivFun.symm (b.equivFun ((toWeakSpace ℝ H).symm x))) =
        ((toWeakSpace ℝ H).symm : WeakSpace ℝ H → H) := by
    funext x
    exact b.equivFun.symm_apply_apply _
  rw [← hcomp]
  exact hsymm.comp hcoords

/-- Helper for Fact 2.33: once the weak and strong topologies agree, the weak topology is
metrizable because it is homeomorphic to the norm topology. -/
-- The canonical weak-space equivalence becomes a homeomorphism as soon as its inverse is
-- continuous, so metrizability transfers from the norm topology.
private lemma metrizable_of_weak_symm_continuous
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (h : Continuous ((toWeakSpace ℝ H).symm : WeakSpace ℝ H → H)) :
    MetrizableSpace (WeakSpace ℝ H) := by
  let e : WeakSpace ℝ H ≃ₜ H :=
    { toEquiv := (toWeakSpace ℝ H).symm.toEquiv
      continuous_toFun := h
      continuous_invFun := (toWeakSpaceCLM ℝ H).continuous }
  let _ : MetrizableSpace (WeakSpace ℝ H) := e.isEmbedding.metrizableSpace
  infer_instance

/-- Helper for Fact 2.33: the strong dual of a complete real Hilbert space is a Baire space. -/
-- We bypass slow typeclass search by explicitly upgrading the norm topology on the dual to a
-- complete pseudometric structure, then invoke the standard Baire theorem for completely
-- pseudometrizable spaces.
private lemma strongDual_baireSpace
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    BaireSpace (StrongDual ℝ H) := by
  letI : PseudoMetricSpace (StrongDual ℝ H) := inferInstance
  letI : CompleteSpace (StrongDual ℝ H) := inferInstance
  letI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (StrongDual ℝ H) :=
    PseudoMetricSpace.toIsCompletelPseudoMetrizableSpace
  exact BaireSpace.of_completelyPseudoMetrizable

/-- Helper for Fact 2.33: the span of finitely many strong-dual functionals is closed. -/
-- The Baire-category route ultimately covers the whole dual by countably many finite spans, so we
-- package the closedness of each finite span separately.
private lemma strongDual_span_finset_closed
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (s : Finset (StrongDual ℝ H)) :
    IsClosed (Submodule.span ℝ (s : Set (StrongDual ℝ H)) : Set (StrongDual ℝ H)) := by
  letI : FiniteDimensional ℝ ↥(Submodule.span ℝ (s : Set (StrongDual ℝ H))) :=
    FiniteDimensional.span_finset ℝ s
  exact Submodule.closed_of_finiteDimensional (Submodule.span ℝ (s : Set (StrongDual ℝ H)))

/-- Helper for Fact 2.33: coercing strong-dual elements to plain linear maps preserves membership
in the finite span generated by a finset of functionals. -/
-- The Baire argument naturally produces finite spans inside the strong dual, while
-- `LinearMap.mem_span_iff_bound` works in the plain algebraic dual. This lemma isolates the
-- transport between those two presentations.
private lemma strongDual_span_map_toLinearMap
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (s : Finset (StrongDual ℝ H)) (φ : StrongDual ℝ H) :
    φ.toLinearMap ∈ Submodule.span ℝ
        (Set.range fun i : ↥(s : Set (StrongDual ℝ H)) ↦
          (i : StrongDual ℝ H).toLinearMap) ↔
      φ ∈ Submodule.span ℝ (s : Set (StrongDual ℝ H)) := by
  -- Reindex the span generated by the subtype family as the image of the finite set under the
  -- coercion `StrongDual → LinearMap`.
  have hrange :
      Set.range (fun i : ↥(s : Set (StrongDual ℝ H)) ↦ (i : StrongDual ℝ H).toLinearMap) =
        (((↑) : StrongDual ℝ H → H →ₗ[ℝ] ℝ) '' (s : Set (StrongDual ℝ H))) := by
    ext ψ
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  rw [hrange]
  simpa using
    (Submodule.apply_mem_span_image_iff_mem_span (R := ℝ) (R₂ := ℝ)
      (f := (ContinuousLinearMap.coeLM ℝ : (StrongDual ℝ H) →ₗ[ℝ] H →ₗ[ℝ] ℝ))
      (x := φ) (s := (s : Set (StrongDual ℝ H)))
      (by
        intro g h hgh
        exact ContinuousLinearMap.coe_injective hgh))

/-- Helper for Fact 2.33: one weak basic neighborhood controlled by finitely many coordinates
forces the tested functional to lie in their span. -/
-- The source-proof step is a scaling argument: if a finite weak neighborhood around `0` already
-- sits inside `φ⁻¹(ball 0 1)`, then `φ` is bounded by the corresponding finite supremum seminorm,
-- and `LinearMap.mem_span_iff_bound` turns that bound into span membership.
private lemma finite_span_of_weak_basic_neighborhood_control
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (s : Finset (StrongDual ℝ H)) (ε : ℝ) (hε : 0 < ε) (φ : StrongDual ℝ H)
    (hU : ((s.sup ((topDualPairing ℝ H).flip.toSeminormFamily)).ball 0 ε) ⊆
      φ ⁻¹' Metric.ball (0 : ℝ) 1) :
    φ ∈ Submodule.span ℝ (s : Set (StrongDual ℝ H)) := by
  by_cases hs : s.Nonempty
  · letI : Nonempty ↥(s : Set (StrongDual ℝ H)) := hs.to_subtype
    let p : Seminorm ℝ H := s.sup ((topDualPairing ℝ H).flip.toSeminormFamily)
    let c : NNReal := ⟨2 / ε, by positivity⟩
    have hsattach :
        s.attach.sup (fun i ↦ (((i : StrongDual ℝ H).toLinearMap).toSeminorm)) = p := by
      exact Finset.sup_attach s fun i ↦ (((i : StrongDual ℝ H).toLinearMap).toSeminorm)
    -- Convert the neighborhood control into the seminorm bound required by
    -- `LinearMap.mem_span_iff_bound`.
    have hlin :
        φ.toLinearMap ∈ Submodule.span ℝ
          (Set.range fun i : ↥(s : Set (StrongDual ℝ H)) ↦
            (i : StrongDual ℝ H).toLinearMap) := by
      rw [LinearMap.mem_span_iff_bound]
      refine ⟨s.attach, ⟨c, ?_⟩⟩
      intro x
      by_cases hx0 : p x = 0
      · -- If the controlling seminorm vanishes on `x`, then every scalar multiple of `x` stays in
        -- the weak basic neighborhood, so `φ x` must vanish as well.
        have hφx0 : φ x = 0 := by
          by_contra hne
          have hnormpos : 0 < ‖φ x‖ := norm_pos_iff.mpr hne
          let t : ℝ := 2 / ‖φ x‖
          have ht : 0 < t := by
            dsimp [t]
            positivity
          have hmem : t • x ∈ p.ball 0 ε := by
            rw [p.mem_ball_zero, map_smul_eq_mul, Real.norm_of_nonneg (le_of_lt ht), hx0]
            simpa using hε
          have hball : t • φ x ∈ Metric.ball (0 : ℝ) 1 := by
            simpa [p, φ.map_smul] using hU hmem
          have hlt : ‖t • φ x‖ < 1 := by
            simpa [Metric.mem_ball, Real.dist_eq] using hball
          have htwo : ‖t • φ x‖ = 2 := by
            have hmul : t * ‖φ x‖ = 2 := by
              dsimp [t]
              field_simp [hnormpos.ne']
            simpa [norm_smul, Real.norm_of_nonneg (le_of_lt ht)] using hmul
          nlinarith [hlt, htwo]
        have hmain : ‖φ x‖ ≤ ((c : ℝ) * p x) := by
          rw [hφx0, norm_zero, hx0]
          simp [c]
        simpa [LinearMap.toSeminorm_apply, hsattach] using hmain
      · -- If the finite supremum seminorm is positive at `x`, scale `x` into the basic
        -- neighborhood and read off a quantitative bound on `φ x`.
        have hpxpos : 0 < p x :=
          lt_of_le_of_ne (apply_nonneg p x) (by simpa [eq_comm] using hx0)
        let t : ℝ := ε / (2 * p x)
        have ht : 0 < t := by
          dsimp [t]
          positivity
        have hmem : t • x ∈ p.ball 0 ε := by
          rw [p.mem_ball_zero, map_smul_eq_mul, Real.norm_of_nonneg (le_of_lt ht)]
          have hhalf : ε / (2 * p x) * p x = ε / 2 := by
            field_simp [ne_of_gt hpxpos]
          rw [show t = ε / (2 * p x) by rfl, hhalf]
          nlinarith
        have hball : t • φ x ∈ Metric.ball (0 : ℝ) 1 := by
          simpa [p, φ.map_smul] using hU hmem
        have hlt : ‖t • φ x‖ < 1 := by
          simpa [Metric.mem_ball, Real.dist_eq] using hball
        have hprod : ε * ‖φ x‖ < 2 * p x := by
          rw [norm_smul, Real.norm_of_nonneg (le_of_lt ht), show t = ε / (2 * p x) by rfl] at hlt
          field_simp [hε.ne', ne_of_gt hpxpos] at hlt
          nlinarith
        have hdiv : ‖φ x‖ < (2 * p x) / ε := by
          exact (lt_div_iff₀ hε).2
            (by simpa [mul_comm, mul_left_comm, mul_assoc] using hprod)
        have hmain : ‖φ x‖ ≤ ((c : ℝ) * p x) := by
          have : ‖φ x‖ < (2 / ε) * p x := by
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
          exact this.le
        simpa [LinearMap.toSeminorm_apply, hsattach] using hmain
    exact (strongDual_span_map_toLinearMap s φ).mp hlin
  · have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    -- If the finite family is empty, the basic neighborhood is all of `H`, so `φ` must vanish.
    have hzero : φ = 0 := by
      ext x
      change φ x = 0
      by_contra hne
      have hnormpos : 0 < ‖φ x‖ := norm_pos_iff.mpr hne
      let t : ℝ := 2 / ‖φ x‖
      have ht : 0 < t := by
        dsimp [t]
        positivity
      have hball : t • φ x ∈ Metric.ball (0 : ℝ) 1 := by
        have hmem : t • x ∈ ((s.sup ((topDualPairing ℝ H).flip.toSeminormFamily)).ball 0 ε) := by
          simp [hs', hε]
        simpa [φ.map_smul] using hU hmem
      have hlt : ‖t • φ x‖ < 1 := by
        simpa [Metric.mem_ball, Real.dist_eq] using hball
      have htwo : ‖t • φ x‖ = 2 := by
        have hmul : t * ‖φ x‖ = 2 := by
          dsimp [t]
          field_simp [hnormpos.ne']
        simpa [norm_smul, Real.norm_of_nonneg (le_of_lt ht)] using hmul
      nlinarith [hlt, htwo]
    simp [hs', hzero]

/-- Helper for Fact 2.33: a countable weak neighborhood basis at `0` covers the strong dual by the
finite spans of the corresponding coordinate families. -/
-- Each strong-dual functional is weakly continuous, so one basis neighborhood is mapped inside the
-- unit ball of `ℝ`. The previous helper then places that functional in the matching finite span.
private lemma strongDual_covered_by_countable_basis_spans
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (s : ℕ → Finset (StrongDual ℝ H)) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n)
    (hbasis : (nhds (0 : WeakSpace ℝ H)).HasAntitoneBasis
      fun n ↦ ((s n).sup ((topDualPairing ℝ H).flip.toSeminormFamily)).ball 0 (ε n)) :
    ⋃ n, (Submodule.span ℝ (s n : Set (StrongDual ℝ H)) : Set (StrongDual ℝ H)) = Set.univ := by
  ext φ
  constructor
  · intro _
    simp
  · -- Weak continuity of the evaluation map lets us trap `φ` inside one basic neighborhood.
    intro _
    have hcont : Continuous fun x : WeakSpace ℝ H ↦ φ x := by
      simpa [WeakSpace, LinearMap.flip_apply, topDualPairing_apply] using
        (WeakBilin.eval_continuous ((topDualPairing ℝ H).flip) φ)
    have hpre : φ ⁻¹' Metric.ball (0 : ℝ) 1 ∈ nhds (0 : WeakSpace ℝ H) := by
      simpa using hcont.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (φ 0) zero_lt_one)
    rcases hbasis.mem_iff.mp hpre with ⟨n, hn⟩
    have hφ :
        φ ∈ (Submodule.span ℝ (s n : Set (StrongDual ℝ H)) : Set (StrongDual ℝ H)) :=
      finite_span_of_weak_basic_neighborhood_control (s n) (ε n) (hε n) φ hn
    exact Set.mem_iUnion.mpr
      ⟨n, (show φ ∈ (Submodule.span ℝ (s n : Set (StrongDual ℝ H)) : Set (StrongDual ℝ H))
        from hφ)⟩

/-- Helper for Fact 2.33: if the weak topology of a real Hilbert space is metrizable, then the
space is finite-dimensional. -/
-- Route correction: the easy finite-dimensional and homeomorphism steps are already settled above.
-- The remaining obstruction is the genuinely structural `(4) → (1)` argument. The stable route is
-- now the countable weak-basis/Baire argument on `StrongDual ℝ H`: extract a countable weak basis
-- at `0`, convert each basic neighborhood into a finite set of coordinates, cover the dual by the
-- corresponding finite spans, and then use the two helpers above to run Baire category on that
-- closed cover.
private lemma finiteDimensional_of_metrizable_weakSpace
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (hmetr : MetrizableSpace (WeakSpace ℝ H)) :
    FiniteDimensional ℝ H := by
  letI : MetrizableSpace (WeakSpace ℝ H) := hmetr
  haveI : BaireSpace (StrongDual ℝ H) := strongDual_baireSpace
  -- Route correction: keep the Baire-category skeleton, but package the finite-step bridge through
  -- the previous span and cover helpers instead of repeating coercion manipulations inline.
  haveI : (nhds (0 : WeakSpace ℝ H)).IsCountablyGenerated := by infer_instance
  -- Extract an antitone countable basis of weak neighborhoods at `0`.
  obtain ⟨u, hu_pos, hu_basis⟩ :=
    (show (nhds (0 : WeakSpace ℝ H)).HasBasis
        (fun sr : Finset (StrongDual ℝ H) × ℝ ↦ 0 < sr.2)
        (fun sr ↦
          (sr.1.sup ((topDualPairing ℝ H).flip.toSeminormFamily)).ball 0 sr.2) from
        @WithSeminorms.hasBasis_zero_ball ℝ (WeakSpace ℝ H) (StrongDual ℝ H) _ 
          (WeakSpace.instAddCommGroup (𝕜 := ℝ) (E := H))
          (WeakSpace.instModule' (𝕜 := ℝ) (𝕝 := ℝ) (E := H))
          _ (((topDualPairing ℝ H).flip).toSeminormFamily)
          (LinearMap.weakBilin_withSeminorms ((topDualPairing ℝ H).flip))).exists_antitone_subbasis
  let s : ℕ → Finset (StrongDual ℝ H) := fun n ↦ (u n).1
  let ε : ℕ → ℝ := fun n ↦ (u n).2
  -- The previous helper turns that basis into a countable closed cover of the strong dual.
  have hcover :
      ⋃ n, (Submodule.span ℝ (s n : Set (StrongDual ℝ H)) : Set (StrongDual ℝ H)) = Set.univ := by
    exact strongDual_covered_by_countable_basis_spans s ε hu_pos hu_basis
  have hclosed :
      ∀ n, IsClosed (Submodule.span ℝ (s n : Set (StrongDual ℝ H)) : Set (StrongDual ℝ H)) := by
    intro n
    exact strongDual_span_finset_closed (s n)
  -- Baire forces one finite span to have nonempty interior, hence to equal the whole dual.
  obtain ⟨n, hn⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  have htop : Submodule.span ℝ (s n : Set (StrongDual ℝ H)) = ⊤ :=
    Submodule.eq_top_of_nonempty_interior' _ hn
  letI : FiniteDimensional ℝ ↥(Submodule.span ℝ (s n : Set (StrongDual ℝ H))) :=
    FiniteDimensional.span_finset ℝ (s n)
  let f :
      ↥(Submodule.span ℝ (s n : Set (StrongDual ℝ H))) →ₗ[ℝ] StrongDual ℝ H :=
    (Submodule.span ℝ (s n : Set (StrongDual ℝ H))).subtype
  have hsurj :
      Function.Surjective f := by
    intro φ
    refine ⟨⟨φ, ?_⟩, rfl⟩
    simp [htop]
  haveI : FiniteDimensional ℝ (StrongDual ℝ H) :=
    FiniteDimensional.of_surjective
      (V := ↥(Submodule.span ℝ (s n : Set (StrongDual ℝ H)))) f hsurj
  -- The Hilbert-space Riesz map is injective, so finite dimensionality transfers back to `H`.
  exact FiniteDimensional.of_injective (InnerProductSpace.toDual ℝ H).toLinearEquiv.toLinearMap
    (InnerProductSpace.toDual ℝ H).injective

/-- Fact 2.33: for a real Hilbert space, the following are equivalent: finite dimensionality,
compactness of the closed unit ball in the norm topology, coincidence of the weak and strong
topologies (expressed as continuity of the canonical map from the weak space back to the normed
space), and metrizability of the weak topology. -/
-- Proof sketch: prove the cycle `(1) → (2) → (1) → (3) → (4) → (1)`. Finite-dimensional normed
-- spaces have compact closed balls, while strong compactness of the unit ball forces finite
-- dimensionality by a Riesz-lemma argument. If `H` is finite-dimensional, then the weak topology
-- agrees with the norm topology, so the inverse of `toWeakSpace ℝ H` is continuous and the weak
-- topology is metrizable. Conversely, in an infinite-dimensional Hilbert space the weak topology
-- is not metrizable.
theorem realHilbertSpace_tfae_finiteDimensional_compactUnitBall_weakTopology
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    List.TFAE
      [FiniteDimensional ℝ H,
        IsCompact (Metric.closedBall (0 : H) 1),
        Continuous ((toWeakSpace ℝ H).symm : WeakSpace ℝ H → H),
        MetrizableSpace (WeakSpace ℝ H)] := by
  -- We compare every clause directly with finite dimensionality, which keeps the outer `TFAE`
  -- argument flat and isolates the only hard direction in one helper lemma.
  refine List.tfae_of_forall (FiniteDimensional ℝ H) _ ?_
  intro p hp
  repeat' rw [List.mem_cons] at hp
  have hp' :
      (p ↔ FiniteDimensional ℝ H) ∨
        (p ↔ IsCompact (Metric.closedBall (0 : H) 1)) ∨
        (p ↔ Continuous ((toWeakSpace ℝ H).symm : WeakSpace ℝ H → H)) ∨
        (p ↔ MetrizableSpace (WeakSpace ℝ H)) := by
    simpa using hp
  rcases hp' with hpfd | hpball | hpweak | hpmetr
  · exact hpfd
  · refine hpball.trans ?_
    constructor
    · -- Strong compactness of the unit ball forces finite dimensionality by Riesz' theorem.
      intro hball
      exact FiniteDimensional.of_isCompact_closedBall ℝ zero_lt_one hball
    · -- In finite dimension, closed balls are compact because the space is proper.
      intro hfd
      letI := hfd
      letI : ProperSpace H := FiniteDimensional.proper ℝ H
      simpa using isCompact_closedBall (0 : H) 1
  · refine hpweak.trans ?_
    constructor
    · -- If the weak and strong topologies coincide, the weak topology is metrizable; the remaining
      -- finite-dimensionality step is deferred to the dedicated helper above.
      intro hcont
      exact finiteDimensional_of_metrizable_weakSpace (metrizable_of_weak_symm_continuous hcont)
    · -- Finite dimensionality gives the finite-coordinate proof that weak and strong topologies
      -- agree.
      intro hfd
      letI := hfd
      exact weak_symm_continuous_of_finiteDimensional
  · refine hpmetr.trans ?_
    constructor
    · -- The hard direction `(4) → (1)` is exactly the metrizable-weak-space helper.
      exact finiteDimensional_of_metrizable_weakSpace
    · -- Once weak and strong topologies agree in finite dimension, metrizability follows.
      intro hfd
      letI := hfd
      exact metrizable_of_weak_symm_continuous weak_symm_continuous_of_finiteDimensional

end

/-! Source item: Chap02/Fact_2_34 -/

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable section

/-- Helper for Facts 2.34 and 2.35: the inverse Riesz map from the weak dual back to `H`
equipped with the weak topology. -/
private def rieszFromWeakDual : WeakDual ℝ H → WeakSpace ℝ H :=
  fun φ ↦ toWeakSpace ℝ H ((InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual φ))

/-- Helper for Facts 2.34, 2.35, and 2.37: the Riesz map from `H` with the weak topology to the
weak dual. -/
private def weakSpaceToWeakDual : WeakSpace ℝ H → WeakDual ℝ H :=
  fun x ↦ StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H ((toWeakSpace ℝ H).symm x))

/-- Helper for Facts 2.34 and 2.35: the inverse Riesz map is continuous. -/
private theorem rieszFromWeakDual_continuous :
    Continuous (rieszFromWeakDual : WeakDual ℝ H → WeakSpace ℝ H) := by
  -- Continuity into the weak topology is checked coordinatewise against continuous linear
  -- functionals.
  refine continuous_induced_rng.2 ?_
  change Continuous (fun φ : WeakDual ℝ H ↦
    fun l : StrongDual ℝ H ↦ l ((toWeakSpace ℝ H).symm (rieszFromWeakDual φ)))
  rw [continuous_pi_iff]
  intro l
  let z : H := (InnerProductSpace.toDual ℝ H).symm l
  have hz : ∀ φ : WeakDual ℝ H,
      l ((toWeakSpace ℝ H).symm (rieszFromWeakDual φ)) = φ z := by
    intro φ
    -- The `l`-coordinate becomes evaluation of `φ` at the Riesz representer of `l`.
    simp only [rieszFromWeakDual, LinearEquiv.symm_apply_apply]
    rw [← InnerProductSpace.toDual_symm_apply]
    rw [real_inner_comm]
    rw [InnerProductSpace.toDual_symm_apply]
    simp [z]
  simpa [hz, z] using (WeakDual.eval_continuous z)

/-- Helper for Facts 2.34, 2.35, and 2.37: the Riesz map is continuous from `H` with the weak
topology to the weak dual. -/
private theorem weakSpaceToWeakDual_continuous :
    Continuous (weakSpaceToWeakDual : WeakSpace ℝ H → WeakDual ℝ H) := by
  -- Continuity into the weak dual is checked coordinatewise by evaluation at vectors.
  apply WeakDual.continuous_of_continuous_eval
  intro y
  simpa [real_inner_comm, weakSpaceToWeakDual, InnerProductSpace.toDual_apply_apply] using
    (WeakBilin.eval_continuous ((topDualPairing ℝ H).flip)
      (StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H y)))

/-- Helper for Facts 2.34, 2.35, and 2.37: composing the inverse Riesz map with the forward one
recovers the original weak vector. -/
private theorem rieszFromWeakDual_weakSpaceToWeakDual (x : WeakSpace ℝ H) :
    rieszFromWeakDual (weakSpaceToWeakDual x) = x := by
  -- This is the standard `symm_apply_apply` identity for the Riesz equivalence.
  change toWeakSpace ℝ H
      ((InnerProductSpace.toDual ℝ H).symm
        (InnerProductSpace.toDual ℝ H ((toWeakSpace ℝ H).symm x))) = x
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact LinearEquiv.apply_symm_apply (toWeakSpace ℝ H) x

/-- Helper for Facts 2.34, 2.35, and 2.37: composing the forward Riesz map with the inverse one
recovers the original weak dual point. -/
private theorem weakSpaceToWeakDual_rieszFromWeakDual (φ : WeakDual ℝ H) :
    weakSpaceToWeakDual (rieszFromWeakDual φ) = φ := by
  -- Equality of weak dual points is checked on all vectors.
  apply DFunLike.ext
  intro y
  simp [weakSpaceToWeakDual, rieszFromWeakDual]

/-- Helper for Facts 2.34, 2.35, and 2.37: the Riesz representation theorem identifies the weak
topology on a real Hilbert space with the weak-* topology on its dual. -/
def weakSpaceHomeomorphWeakDual : WeakSpace ℝ H ≃ₜ WeakDual ℝ H :=
  { toEquiv :=
      { toFun := weakSpaceToWeakDual
        invFun := rieszFromWeakDual
        left_inv := rieszFromWeakDual_weakSpaceToWeakDual
        right_inv := weakSpaceToWeakDual_rieszFromWeakDual }
    continuous_toFun := weakSpaceToWeakDual_continuous
    continuous_invFun := rieszFromWeakDual_continuous }

@[simp]
theorem weakSpaceHomeomorphWeakDual_apply (x : WeakSpace ℝ H) :
    weakSpaceHomeomorphWeakDual x =
      StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H ((toWeakSpace ℝ H).symm x)) :=
  rfl

@[simp]
theorem weakSpaceHomeomorphWeakDual_symm_apply (φ : WeakDual ℝ H) :
    weakSpaceHomeomorphWeakDual.symm φ =
      toWeakSpace ℝ H ((InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual φ)) :=
  rfl

private lemma rieszFromWeakDual_image_closedBall :
    rieszFromWeakDual ''
        (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) 1) =
      ((toWeakSpace ℝ H) '' Metric.closedBall (0 : H) 1 : Set (WeakSpace ℝ H)) := by
  ext x
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    refine ⟨(InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual φ), ?_, ?_⟩
    · -- The inverse Riesz map preserves norms, so membership in the dual closed ball transports
      -- to membership in the Hilbert-space closed ball.
      simpa [Metric.mem_closedBall, dist_eq_norm, ((InnerProductSpace.toDual ℝ H).symm).norm_map]
        using hφ
    · simp [rieszFromWeakDual]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H y), ?_, ?_⟩
    · -- The forward Riesz map is also an isometry, so vectors in the Hilbert-space unit ball map
      -- into the dual closed unit ball.
      have hy' : ‖InnerProductSpace.toDual ℝ H y‖ ≤ 1 := by
        simpa [(InnerProductSpace.toDual ℝ H).norm_map, Metric.mem_closedBall, dist_eq_norm]
          using hy
      change WeakDual.toStrongDual (StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H y)) ∈
        Metric.closedBall (0 : StrongDual ℝ H) 1
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      change ‖InnerProductSpace.toDual ℝ H y‖ ≤ 1
      exact hy'
    · change (InnerProductSpace.toDual ℝ H).symm ((InnerProductSpace.toDual ℝ H) y) = y
      simp

/-- Fact 2.34: the closed unit ball of a real Hilbert space is compact for the weak topology.
This is the Banach--Alaoglu--Bourbaki compactness statement in the Hilbert-space setting. -/
-- Proof sketch: transport the weak topology on `H` to the weak-* topology on the continuous dual
-- via the Fréchet-Riesz isometric equivalence `InnerProductSpace.toDual ℝ H`, identify the image of
-- the unit ball with the weak-* closed unit ball in the dual, and apply
-- `WeakDual.isCompact_closedBall`.
theorem isCompact_unitBall_weakSpace :
    IsCompact ((toWeakSpace ℝ H) '' Metric.closedBall (0 : H) 1 : Set (WeakSpace ℝ H)) := by
  let dualBall : Set (WeakDual ℝ H) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) 1
  -- Banach-Alaoglu gives weak-* compactness of the dual closed unit ball.
  have hcompact : IsCompact dualBall :=
    WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) 1
  -- The inverse Riesz map sends that compact set onto the weak unit ball in `H`.
  have himage : IsCompact (rieszFromWeakDual '' dualBall) :=
    hcompact.image rieszFromWeakDual_continuous
  convert himage using 1
  symm
  exact rieszFromWeakDual_image_closedBall

end

/-! Source item: Chap02/Fact_2_35 -/

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The closed unit ball of a real Hilbert space, viewed with the weak subspace topology. -/
abbrev weakClosedUnitBall (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :=
  {x : WeakSpace ℝ H // ‖(toWeakSpace ℝ H).symm x‖ ≤ 1}

/-- Every point of `weakClosedUnitBall H` has underlying norm at most `1`. -/
theorem weakClosedUnitBall_norm_le_one (x : weakClosedUnitBall H) :
    ‖(toWeakSpace ℝ H).symm x‖ ≤ 1 := by
  -- The closed-ball inequality is exactly the subtype predicate.
  exact x.2

/-- Helper for Fact 2.35: the normalized vector `x / ‖x‖` belongs to the weak closed unit ball
whenever `x ≠ 0`. -/
private theorem normalized_mem_weakClosedUnitBall (x : H) (hx : x ≠ 0) :
    ‖(‖x‖)⁻¹ • x‖ ≤ 1 := by
  -- Normalization places the vector on the unit sphere.
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  exact le_of_eq (inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx))

/-- Helper for Fact 2.35: the normalized nonzero vector as a point of the weak closed unit ball. -/
private def normalizedWeakClosedUnitBall (x : H) (hx : x ≠ 0) :
    weakClosedUnitBall H :=
  ⟨toWeakSpace ℝ H ((‖x‖)⁻¹ • x), normalized_mem_weakClosedUnitBall x hx⟩

section Complete

variable [CompleteSpace H]

/-- Helper for Fact 2.35: the weak-* closed unit ball in the continuous dual of `H`. -/
private abbrev weakDualClosedUnitBall (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] :=
  {φ : WeakDual ℝ H // WeakDual.toStrongDual φ ∈ Metric.closedBall (0 : StrongDual ℝ H) 1}

/-- Helper for Fact 2.35: the Fréchet-Riesz map sends the weak closed unit ball of `H` into the
weak-* closed unit ball of the dual. -/
private theorem weakClosedUnitBall_toWeakDual_mem (x : weakClosedUnitBall H) :
    WeakDual.toStrongDual
        (weakSpaceHomeomorphWeakDual (x : WeakSpace ℝ H)) ∈
      Metric.closedBall (0 : StrongDual ℝ H) 1 := by
  -- The Riesz map is an isometry, so the norm bound is transported unchanged.
  have hx : ‖WeakDual.toStrongDual
      (weakSpaceHomeomorphWeakDual (x : WeakSpace ℝ H))‖ ≤ 1 := by
    change ‖InnerProductSpace.toDual ℝ H ((toWeakSpace ℝ H).symm x)‖ ≤ 1
    rw [(InnerProductSpace.toDual ℝ H).norm_map]
    exact weakClosedUnitBall_norm_le_one x
  simpa [Metric.mem_closedBall, dist_eq_norm] using hx

/-- Helper for Fact 2.35: the inverse Riesz map sends the weak-* dual closed unit ball back to the
weak closed unit ball of `H`. -/
private theorem weakDualClosedUnitBall_toWeakClosedUnitBall_mem (φ : weakDualClosedUnitBall H) :
    ‖(toWeakSpace ℝ H).symm (weakSpaceHomeomorphWeakDual.symm (φ : WeakDual ℝ H))‖ ≤ 1 := by
  -- Again, the inverse Riesz map preserves the norm.
  have hφ : ‖WeakDual.toStrongDual (φ : WeakDual ℝ H)‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using φ.2
  change ‖(InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual (φ : WeakDual ℝ H))‖ ≤ 1
  rw [((InnerProductSpace.toDual ℝ H).symm).norm_map]
  exact hφ

/-- Helper for Fact 2.35: weak inner-product coordinates are continuous on `H` equipped with the
weak topology. -/
theorem weakSpace_continuous_inner_right (y : H) :
    Continuous fun x : WeakSpace ℝ H ↦ inner ℝ ((toWeakSpace ℝ H).symm x) y := by
  -- Coordinate maps in the weak topology are continuous by definition, and in the Hilbert-space
  -- setting the Riesz map identifies them with inner products against fixed vectors.
  simpa [real_inner_comm, InnerProductSpace.toDual_apply_apply] using
    (WeakBilin.eval_continuous ((topDualPairing ℝ H).flip)
      (weakSpaceHomeomorphWeakDual (toWeakSpace ℝ H y)))

/-- Helper for Fact 2.35: the forward Riesz map restricted to the weak closed unit ball. -/
private def weakClosedUnitBallToWeakDualClosedUnitBall :
    weakClosedUnitBall H → weakDualClosedUnitBall H :=
  fun x ↦ ⟨weakSpaceHomeomorphWeakDual (x : WeakSpace ℝ H), weakClosedUnitBall_toWeakDual_mem x⟩

/-- Helper for Fact 2.35: the inverse Riesz map restricted to the weak-* dual closed unit ball. -/
private def weakDualClosedUnitBallToWeakClosedUnitBall :
    weakDualClosedUnitBall H → weakClosedUnitBall H :=
  fun φ ↦
    ⟨weakSpaceHomeomorphWeakDual.symm (φ : WeakDual ℝ H),
      weakDualClosedUnitBall_toWeakClosedUnitBall_mem φ⟩

/-- Helper for Fact 2.35: the restricted forward Riesz map is continuous. -/
private theorem weakClosedUnitBallToWeakDualClosedUnitBall_continuous :
    Continuous (weakClosedUnitBallToWeakDualClosedUnitBall :
      weakClosedUnitBall H → weakDualClosedUnitBall H) := by
  -- We just compose the continuous whole-space map with the subtype inclusion.
  apply Continuous.subtype_mk
  exact weakSpaceHomeomorphWeakDual.continuous.comp continuous_subtype_val

/-- Helper for Fact 2.35: the restricted inverse Riesz map is continuous. -/
private theorem weakDualClosedUnitBallToWeakClosedUnitBall_continuous :
    Continuous (weakDualClosedUnitBallToWeakClosedUnitBall :
      weakDualClosedUnitBall H → weakClosedUnitBall H) := by
  -- The same argument works for the inverse map.
  apply Continuous.subtype_mk
  exact weakSpaceHomeomorphWeakDual.symm.continuous.comp continuous_subtype_val

/-- Helper for Fact 2.35: the restricted inverse Riesz map is a left inverse to the restricted
forward map. -/
private theorem weakDualClosedUnitBall_left_inv (x : weakClosedUnitBall H) :
    weakDualClosedUnitBallToWeakClosedUnitBall
        (weakClosedUnitBallToWeakDualClosedUnitBall x) = x := by
  -- Equality of subtype points reduces to equality of their ambient weak vectors.
  apply Subtype.ext
  exact weakSpaceHomeomorphWeakDual.left_inv (x : WeakSpace ℝ H)

/-- Helper for Fact 2.35: the restricted forward Riesz map is a right inverse to the restricted
inverse map. -/
private theorem weakClosedUnitBall_right_inv (φ : weakDualClosedUnitBall H) :
    weakClosedUnitBallToWeakDualClosedUnitBall
        (weakDualClosedUnitBallToWeakClosedUnitBall φ) = φ := by
  -- Again, equality is checked on the ambient weak-* functionals.
  apply Subtype.ext
  exact weakSpaceHomeomorphWeakDual.right_inv (φ : WeakDual ℝ H)

/-- Helper for Fact 2.35: the weak closed unit ball of `H` is homeomorphic to the weak-* closed
unit ball of the dual via the Riesz representation theorem. -/
private def weakClosedUnitBall_homeomorph_weakDual_closedBall :
    weakClosedUnitBall H ≃ₜ weakDualClosedUnitBall H :=
  { toEquiv :=
      { toFun := weakClosedUnitBallToWeakDualClosedUnitBall
        invFun := weakDualClosedUnitBallToWeakClosedUnitBall
        left_inv := weakDualClosedUnitBall_left_inv
        right_inv := weakClosedUnitBall_right_inv }
    continuous_toFun := weakClosedUnitBallToWeakDualClosedUnitBall_continuous
    continuous_invFun := weakDualClosedUnitBallToWeakClosedUnitBall_continuous }

private instance : CompactSpace (weakDualClosedUnitBall H) := by
  let K : Set (WeakDual ℝ H) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) 1
  have hK : IsCompact K := WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) 1
  simpa [weakDualClosedUnitBall, K, isCompact_iff_compactSpace] using
    (isCompact_iff_compactSpace.mp hK)

/-- Helper for Fact 2.35: the weak closed unit ball is a compact space. -/
instance : CompactSpace (weakClosedUnitBall H) :=
  weakClosedUnitBall_homeomorph_weakDual_closedBall.symm.compactSpace

/-- Helper for Fact 2.35: the evaluation map sending `x` to the weak-coordinate function
`u ↦ ⟪u, x⟫` on the weak closed unit ball. -/
def evalOnWeakClosedUnitBall (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] :
    H → C(weakClosedUnitBall H, ℝ) :=
  fun x ↦
    { toFun := fun u ↦ inner ℝ ((toWeakSpace ℝ H).symm u) x
      continuous_toFun := (weakSpace_continuous_inner_right x).comp continuous_subtype_val }

/-- Helper for Fact 2.35: the evaluation map is additive, hence it respects subtraction. -/
private theorem evalOnWeakClosedUnitBall_sub (x y : H) :
    evalOnWeakClosedUnitBall H (x - y) =
      evalOnWeakClosedUnitBall H x - evalOnWeakClosedUnitBall H y := by
  -- Pointwise subtraction is just linearity of the inner product in the second slot.
  ext u
  simp [evalOnWeakClosedUnitBall, inner_sub_right]

/-- Helper for Fact 2.35: the evaluation map has norm exactly `‖x‖`. -/
theorem evalOnWeakClosedUnitBall_norm_eq (x : H) :
    ‖evalOnWeakClosedUnitBall H x‖ = ‖x‖ := by
  -- The upper bound comes from Cauchy-Schwarz and the unit-ball constraint.
  have hub : ‖evalOnWeakClosedUnitBall H x‖ ≤ ‖x‖ := by
    rw [ContinuousMap.norm_le (evalOnWeakClosedUnitBall H x) (norm_nonneg x)]
    intro u
    have hu : ‖(toWeakSpace ℝ H).symm u‖ * ‖x‖ ≤ 1 * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right (weakClosedUnitBall_norm_le_one u) (norm_nonneg x)
    calc
      ‖evalOnWeakClosedUnitBall H x u‖
          = |inner ℝ ((toWeakSpace ℝ H).symm u) x| := rfl
      _ ≤ ‖(toWeakSpace ℝ H).symm u‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * ‖x‖ := hu
      _ = ‖x‖ := by ring
  by_cases hx : x = 0
  · -- At the zero vector the norm identity is immediate.
    subst hx
    have hzero : evalOnWeakClosedUnitBall H (0 : H) = 0 := by
      ext u
      simp [evalOnWeakClosedUnitBall]
    rw [hzero]
    simp
  · -- Route correction: for the lower bound we test the function at the normalized vector
    -- `x / ‖x‖`, which lies in the weak closed unit ball.
    let u : weakClosedUnitBall H := normalizedWeakClosedUnitBall x hx
    have hu_eval : evalOnWeakClosedUnitBall H x u = ‖x‖ := by
      -- Evaluating at the normalized vector achieves the operator norm exactly.
      change inner ℝ ((‖x‖)⁻¹ • x) x = ‖x‖
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp [norm_ne_zero_iff.mpr hx]
    have hlow : ‖x‖ ≤ ‖evalOnWeakClosedUnitBall H x‖ := by
      simpa [hu_eval] using ContinuousMap.norm_coe_le_norm (evalOnWeakClosedUnitBall H x) u
    exact le_antisymm hub hlow

/-- Helper for Fact 2.35: the evaluation embedding of `H` into continuous functions on the weak
closed unit ball is an isometry. -/
private theorem evalOnWeakClosedUnitBall_isometry : Isometry (evalOnWeakClosedUnitBall H) := by
  -- Distances are computed by the norm of the difference, and the previous norm formula applies
  -- to that difference.
  refine Isometry.of_dist_eq fun x y ↦ ?_
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖evalOnWeakClosedUnitBall H x - evalOnWeakClosedUnitBall H y‖
        = ‖evalOnWeakClosedUnitBall H (x - y)‖ := by
            rw [← evalOnWeakClosedUnitBall_sub]
    _ = ‖x - y‖ := evalOnWeakClosedUnitBall_norm_eq (x - y)

/-- Fact 2.35: the weak topology on the closed unit ball of a real Hilbert space is metrizable if
and only if the Hilbert space is separable. -/
theorem weakClosedUnitBall_metrizable_iff_separable :
    MetrizableSpace (weakClosedUnitBall H) ↔ SeparableSpace H := by
  constructor
  · intro hmetr
    -- Compactness plus metrizability makes the weak closed unit ball second countable, so the
    -- evaluation isometry embeds `H` into the separable space `C(K, ℝ)`.
    letI : MetrizableSpace (weakClosedUnitBall H) := hmetr
    haveI : SecondCountableTopology (weakClosedUnitBall H) := by infer_instance
    haveI : SecondCountableTopology C(weakClosedUnitBall H, ℝ) := by infer_instance
    exact evalOnWeakClosedUnitBall_isometry.isEmbedding.separableSpace
  · intro hsep
    -- The weak ball is homeomorphic to a weak-* compact dual ball, and the latter is metrizable
    -- in the separable case by the countable-separating theorem from mathlib.
    letI : SeparableSpace H := hsep
    let K : Set (WeakDual ℝ H) :=
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) 1
    have hK : IsCompact K := WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) 1
    haveI : MetrizableSpace (weakDualClosedUnitBall H) := by
      simpa [weakDualClosedUnitBall, K] using
        (WeakDual.metrizable_of_isCompact ℝ H K hK)
    exact weakClosedUnitBall_homeomorph_weakDual_closedBall.isEmbedding.metrizableSpace

end Complete

end

/-! Source item: Chap02/Lemma_2_36 -/

noncomputable section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗]

/-- The metric closed unit ball centered at `0` is the norm unit ball. -/
private lemma closedBall_zero_one_eq :
    (Metric.closedBall (0 : 𝓗) 1 : Set 𝓗) = {x : 𝓗 | ‖x‖ ≤ 1} := by
  ext x
  simp [Metric.mem_closedBall, dist_eq_norm]

variable [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

/-- Helper for Lemma 2.36: compactness of the weak image bounds each scalar evaluation coming from
the Riesz family. -/
private lemma pointwise_bounded_riesz_family_of_isCompact
    {C : Set 𝓗} (hC : IsCompact ((toWeakSpace ℝ 𝓗) '' C)) :
    ∀ u : 𝓗, ∃ M : ℝ, ∀ x ∈ C, ‖(InnerProductSpace.toDual ℝ 𝓗 x) u‖ ≤ M := by
  intro u
  let evalAt : WeakSpace ℝ 𝓗 → ℝ :=
    fun z ↦ (InnerProductSpace.toDual ℝ 𝓗 u) ((toWeakSpace ℝ 𝓗).symm z)
  have heval : Continuous evalAt := by
    -- Weak-space coordinates are exactly evaluations against continuous linear functionals.
    simpa [evalAt, WeakSpace, LinearMap.flip_apply, topDualPairing_apply] using
      (WeakBilin.eval_continuous ((topDualPairing ℝ 𝓗).flip)
        (InnerProductSpace.toDual ℝ 𝓗 u))
  obtain ⟨M, hM⟩ := (hC.image heval).isBounded.exists_norm_le
  refine ⟨M, ?_⟩
  intro x hx
  have hxImage : evalAt (toWeakSpace ℝ 𝓗 x) ∈ evalAt '' ((toWeakSpace ℝ 𝓗) '' C) := by
    exact ⟨toWeakSpace ℝ 𝓗 x, ⟨x, hx, rfl⟩, rfl⟩
  have hbound : ‖evalAt (toWeakSpace ℝ 𝓗 x)‖ ≤ M := hM _ hxImage
  -- For real Hilbert spaces, swapping the two arguments of the inner product does not change the
  -- value, so the bound matches the desired Riesz functional.
  simpa [evalAt, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hbound

/-- Helper for Lemma 2.36: a weakly compact set in a real Hilbert space is norm-bounded. -/
private lemma isBounded_of_isCompact_weakImage
    {C : Set 𝓗} (hC : IsCompact ((toWeakSpace ℝ 𝓗) '' C)) :
    Bornology.IsBounded C := by
  let T : C → 𝓗 →L[ℝ] ℝ := fun x ↦ InnerProductSpace.toDual ℝ 𝓗 x.1
  have hpointwise : ∀ u : 𝓗, ∃ M : ℝ, ∀ x : C, ‖T x u‖ ≤ M := by
    intro u
    rcases pointwise_bounded_riesz_family_of_isCompact hC u with ⟨M, hM⟩
    exact ⟨M, fun x ↦ hM x x.2⟩
  obtain ⟨M, hM⟩ := banach_steinhaus hpointwise
  rw [isBounded_iff_forall_norm_le]
  refine ⟨M, ?_⟩
  intro x hx
  have hTx : ‖InnerProductSpace.toDual ℝ 𝓗 x‖ ≤ M := by
    simpa [T] using hM ⟨x, hx⟩
  rw [(InnerProductSpace.toDual ℝ 𝓗).norm_map x] at hTx
  exact hTx

/-- The weak image of any scalar multiple of the closed unit ball is compact. -/
lemma isCompact_weakImage_smul_unit_ball (a : ℝ) :
    IsCompact ((toWeakSpace ℝ 𝓗) '' (a • {x : 𝓗 | ‖x‖ ≤ 1})) := by
  have hunit :
      IsCompact ((toWeakSpace ℝ 𝓗) '' {x : 𝓗 | ‖x‖ ≤ 1} : Set (WeakSpace ℝ 𝓗)) :=
    by
      simpa [closedBall_zero_one_eq] using
        (isCompact_unitBall_weakSpace :
          IsCompact
            ((toWeakSpace ℝ 𝓗) '' Metric.closedBall (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗)))
  have hsmul :
      IsCompact
        (a • ((toWeakSpace ℝ 𝓗) '' {x : 𝓗 | ‖x‖ ≤ 1} : Set (WeakSpace ℝ 𝓗))) :=
    IsCompact.smul a hunit
  -- The canonical weak embedding is linear, so it commutes with scalar multiplication on sets.
  convert hsmul using 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨toWeakSpace ℝ 𝓗 y, ⟨y, hy, rfl⟩, by simp⟩
  · rintro ⟨w, hw, rfl⟩
    rcases hw with ⟨y, hy, rfl⟩
    exact ⟨a • y, ⟨y, hy, rfl⟩, by simp⟩

/-- Lemma 2.36: a subset of a real Hilbert space is weakly compact if and only if it is weakly
closed and norm-bounded. Here weak compactness and weak closedness are expressed by viewing the set
inside `WeakSpace ℝ 𝓗`. -/
-- Proof sketch: for the forward implication, compact subsets of the weak topology are weakly
-- closed because `WeakSpace ℝ 𝓗` is Hausdorff, and compactness of all scalar evaluation images
-- gives pointwise boundedness, which the uniform boundedness principle upgrades to norm
-- boundedness. For the converse, place the bounded set inside a closed ball, use weak compactness
-- of that closed ball in a Hilbert space, and then apply closedness in the weak topology.
theorem weaklyCompact_iff_weaklyClosed_and_bounded {C : Set 𝓗} :
    IsCompact ((toWeakSpace ℝ 𝓗) '' C) ↔
      IsClosed ((toWeakSpace ℝ 𝓗) '' C) ∧ Bornology.IsBounded C := by
  constructor
  · intro hC
    -- Compact subsets of the weak topology are closed, and Banach-Steinhaus upgrades the
    -- coordinatewise compactness bounds to a uniform norm bound.
    exact ⟨hC.isClosed, isBounded_of_isCompact_weakImage hC⟩
  · rintro ⟨hclosed, hbounded⟩
    rcases (NormedSpace.isBounded_iff_subset_smul_closedBall ℝ).1 hbounded with ⟨a, ha⟩
    have hsubset :
        C ⊆ a • {x : 𝓗 | ‖x‖ ≤ 1} := by
      simpa [closedBall_zero_one_eq] using ha
    have hcompactAmbient :
        IsCompact ((toWeakSpace ℝ 𝓗) '' (a • {x : 𝓗 | ‖x‖ ≤ 1})) :=
      isCompact_weakImage_smul_unit_ball a
    -- The weakly closed set sits inside a weakly compact scaled unit ball, hence is weakly
    -- compact as a closed subset.
    refine IsCompact.of_isClosed_subset hcompactAmbient hclosed ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hsubset hx, rfl⟩

end

/-! Source item: Chap02/Fact_2_37 -/

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Fact 2.37: compact weak subsets of a separable real Hilbert space are first
countable. -/
private theorem compact_weak_subset_firstCountable_of_separable
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    [SeparableSpace K] {s : Set (WeakSpace ℝ K)} (hs : IsCompact s) :
    FirstCountableTopology s := by
  -- Transport the compact set to the weak dual, where compact subsets are metrizable in the
  -- separable case.
  let e : WeakSpace ℝ K ≃ₜ WeakDual ℝ K := weakSpaceHomeomorphWeakDual
  have hsImage : IsCompact (e '' s) := hs.image e.continuous
  haveI : MetrizableSpace (e '' s) := WeakDual.metrizable_of_isCompact ℝ K (e '' s) hsImage
  exact (e.image s).isEmbedding.firstCountableTopology

/-- Helper for Fact 2.37: in a separable real Hilbert space, every sequence in a weakly compact
set has a weakly convergent subsequence. -/
private theorem compact_weak_subset_tendsto_subseq_of_separable
    {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    [SeparableSpace K] {s : Set (WeakSpace ℝ K)} (hs : IsCompact s)
    {x : ℕ → WeakSpace ℝ K} (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) := by
  letI := compact_weak_subset_firstCountable_of_separable hs
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  -- On the compact subtype we may use the metric-space compact implies sequential compact theorem.
  let xs : ℕ → s := fun n ↦ ⟨x n, hx n⟩
  rcases CompactSpace.tendsto_subseq xs with ⟨a, φ, hφ, hφ_tendsto⟩
  have hφ_tendsto' :
      Tendsto (fun n ↦ ((xs (φ n)) : WeakSpace ℝ K)) atTop (𝓝 (a : WeakSpace ℝ K)) := by
    exact (continuous_subtype_val.tendsto a).comp hφ_tendsto
  refine ⟨a, a.2, φ, hφ, ?_⟩
  simpa [xs, Function.comp] using hφ_tendsto'

/-- Helper for Fact 2.37: a weakly convergent sequence in a real Hilbert space has norm-bounded
range. -/
private theorem isBounded_range_of_tendsto_weakSpace
    {x : ℕ → H} {y : WeakSpace ℝ H}
    (hy : Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 y)) :
    Bornology.IsBounded (Set.range x) := by
  let T : ℕ → H →L[ℝ] ℝ := fun n ↦ InnerProductSpace.toDual ℝ H (x n)
  have hpointwise : ∀ u : H, ∃ C : ℝ, ∀ n : ℕ, ‖T n u‖ ≤ C := by
    intro u
    -- Weak convergence controls every scalar inner-product coordinate.
    have hu_tendsto :
        Tendsto (fun n ↦ inner ℝ (x n) u) atTop
          (𝓝 (inner ℝ ((toWeakSpace ℝ H).symm y) u)) := by
      simpa using
        (weakSpace_continuous_inner_right (H := H) u).tendsto y |>.comp hy
    have hu_bounded :
        Bornology.IsBounded (Set.range fun n ↦ inner ℝ (x n) u) :=
      Metric.isBounded_range_of_tendsto _ hu_tendsto
    rcases isBounded_iff_forall_norm_le.mp hu_bounded with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro n
    have hCn : ‖inner ℝ (x n) u‖ ≤ C := hC _ (Set.mem_range_self n)
    simpa [T, InnerProductSpace.toDual_apply_apply] using hCn
  -- Banach-Steinhaus upgrades pointwise bounds to a uniform norm bound.
  obtain ⟨C, hC⟩ := uniform_boundedness_principle hpointwise
  rw [isBounded_iff_forall_norm_le]
  refine ⟨C, ?_⟩
  rintro z ⟨n, rfl⟩
  have hTn : ‖T n‖ ≤ C := hC n
  change ‖InnerProductSpace.toDual ℝ H (x n)‖ ≤ C at hTn
  rw [(InnerProductSpace.toDual ℝ H).norm_map] at hTn
  exact hTn

/-- Helper for Fact 2.37: weak sequential compactness forces norm boundedness of the underlying
set in the ambient Hilbert space. -/
private theorem isBounded_preimage_of_isSeqCompact_weakSpace
    {s : Set (WeakSpace ℝ H)} (hs : IsSeqCompact s) :
    Bornology.IsBounded ((toWeakSpace ℝ H).symm '' s) := by
  by_contra hbounded
  rw [isBounded_iff_forall_norm_le] at hbounded
  push Not at hbounded
  have hlargeTerms :
      ∀ n : ℕ, ∃ y ∈ ((toWeakSpace ℝ H).symm '' s), ((n : ℝ) < ‖y‖) := by
    intro n
    exact hbounded n
  choose y hyMem hyNorm using hlargeTerms
  choose x hx_mem hx_eq using fun n ↦ hyMem n
  have hx_mem : ∀ n, x n ∈ s := by
    intro n
    exact hx_mem n
  rcases hs hx_mem with ⟨z, hz, φ, hφ, hφ_tendsto⟩
  have hboundedSubseq :
      Bornology.IsBounded (Set.range fun n ↦ (toWeakSpace ℝ H).symm (x (φ n))) := by
    -- A weakly convergent subsequence is norm-bounded.
    have hweakSubseq :
        Tendsto (fun n ↦ x (φ n)) atTop (𝓝 z) := by
      simpa [Function.comp] using hφ_tendsto
    have hweakSubseq' :
        Tendsto (fun n ↦ toWeakSpace ℝ H ((toWeakSpace ℝ H).symm (x (φ n)))) atTop (𝓝 z) := by
      simpa using hweakSubseq
    simpa using isBounded_range_of_tendsto_weakSpace hweakSubseq'
  rcases isBounded_iff_forall_norm_le.mp hboundedSubseq with ⟨C, hC⟩
  have hC_le : C ≤ (φ ⌈C⌉₊ : ℝ) := by
    have hmono : ⌈C⌉₊ ≤ φ ⌈C⌉₊ := StrictMono.id_le hφ ⌈C⌉₊
    exact le_trans (by exact_mod_cast Nat.le_ceil C) (by exact_mod_cast hmono)
  have hlarge : C < ‖y (φ ⌈C⌉₊)‖ := lt_of_le_of_lt hC_le (hyNorm (φ ⌈C⌉₊))
  have hsmall :
      ‖(toWeakSpace ℝ H).symm (x (φ ⌈C⌉₊))‖ ≤ C := hC _ (Set.mem_range_self ⌈C⌉₊)
  have hxy : (toWeakSpace ℝ H).symm (x (φ ⌈C⌉₊)) = y (φ ⌈C⌉₊) := hx_eq (φ ⌈C⌉₊)
  have hsmall' : ‖y (φ ⌈C⌉₊)‖ ≤ C := by simpa [hxy] using hsmall
  exact (not_lt_of_ge hsmall') hlarge

omit [CompleteSpace H] in
/-- Helper for Fact 2.37: the closed linear span of a sequence range in a real Hilbert space is
separable. -/
private theorem separableSpace_topologicalClosure_span_range (x : ℕ → H) :
    SeparableSpace (Submodule.topologicalClosure (Submodule.span ℝ (Set.range x))) := by
  -- A countable set has separable span, and taking closure preserves separability.
  exact ((Set.countable_range x).isSeparable.span.closure).separableSpace

omit [CompleteSpace H] in
/-- Helper for Fact 2.37: on a closed subspace, inclusion after orthogonal projection is the
identity. -/
private theorem weak_subtype_projection_eq_self_of_mem
    (K : Submodule ℝ H) [CompleteSpace ↥K] {z : WeakSpace ℝ H}
    (hz : (toWeakSpace ℝ H).symm z ∈ K) :
    WeakSpace.map K.subtypeL (WeakSpace.map K.orthogonalProjection z) = z := by
  -- The star projection acts as the identity on vectors already lying in the subspace.
  change toWeakSpace ℝ H ((K.subtypeL (K.orthogonalProjection ((toWeakSpace ℝ H).symm z))) : H) = z
  rw [show K.subtypeL (K.orthogonalProjection ((toWeakSpace ℝ H).symm z)) =
      K.starProjection ((toWeakSpace ℝ H).symm z) by rfl]
  rw [Submodule.starProjection_eq_self_iff.mpr hz]
  exact LinearEquiv.symm_apply_apply (toWeakSpace ℝ H) z

/-- Helper for Fact 2.37: finite weak-coordinate tubes centered at a point form neighborhoods in
`WeakSpace ℝ H`. -/
private theorem weak_coordinate_tube_mem_nhds
    (x : WeakSpace ℝ H) (F : Finset H) {ε : ℝ} (hε : 0 < ε) :
    {w : WeakSpace ℝ H |
      ∀ v ∈ F, |inner ℝ ((toWeakSpace ℝ H).symm w - (toWeakSpace ℝ H).symm x) v| < ε} ∈ 𝓝 x := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha hs =>
      have hsingle :
          {w : WeakSpace ℝ H |
              |inner ℝ ((toWeakSpace ℝ H).symm w - (toWeakSpace ℝ H).symm x) a| < ε} ∈ 𝓝 x := by
        let f : WeakSpace ℝ H → ℝ :=
          fun w ↦ inner ℝ ((toWeakSpace ℝ H).symm w - (toWeakSpace ℝ H).symm x) a
        have hf : Continuous f := by
          -- Weak coordinate maps remain continuous after subtracting the fixed center.
          have hcoord : Continuous fun w : WeakSpace ℝ H ↦
              inner ℝ ((toWeakSpace ℝ H).symm w) a :=
            weakSpace_continuous_inner_right (H := H) a
          simpa [f, inner_sub_left] using hcoord.sub continuous_const
        have hball : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) :=
          Metric.ball_mem_nhds _ hε
        have hpre : f ⁻¹' Metric.ball (0 : ℝ) ε ∈ 𝓝 x :=
          hf.continuousAt.preimage_mem_nhds (by simpa [f] using hball)
        have hset :
            f ⁻¹' Metric.ball (0 : ℝ) ε =
              {w : WeakSpace ℝ H |
                |inner ℝ ((toWeakSpace ℝ H).symm w - (toWeakSpace ℝ H).symm x) a| < ε} := by
          ext w
          simp [f, Metric.mem_ball]
        simpa [hset] using hpre
      have hinter :
          {w : WeakSpace ℝ H |
              ∀ v ∈ insert a s,
                |inner ℝ ((toWeakSpace ℝ H).symm w - (toWeakSpace ℝ H).symm x) v| < ε} =
            {w : WeakSpace ℝ H |
                |inner ℝ ((toWeakSpace ℝ H).symm w - (toWeakSpace ℝ H).symm x) a| < ε} ∩
              {w : WeakSpace ℝ H |
                ∀ v ∈ s, |inner ℝ ((toWeakSpace ℝ H).symm w - (toWeakSpace ℝ H).symm x) v| < ε} := by
        ext w
        simp
      rw [hinter]
      exact inter_mem hsingle hs

omit [CompleteSpace H] in
/-- Helper for Fact 2.37: if orthogonal projection followed by inclusion fixes a weak point, then
the underlying vector already lies in the subspace. -/
private theorem mem_of_weak_subtype_projection_eq_self
    (K : Submodule ℝ H) [CompleteSpace ↥K] {z : WeakSpace ℝ H}
    (hz : WeakSpace.map K.subtypeL (WeakSpace.map K.orthogonalProjection z) = z) :
    (toWeakSpace ℝ H).symm z ∈ K := by
  -- Unfold the weak-space map and use the characterization of the star projection.
  change toWeakSpace ℝ H (K.starProjection ((toWeakSpace ℝ H).symm z)) = z at hz
  exact Submodule.starProjection_eq_self_iff.mp ((toWeakSpace ℝ H).injective hz)

/-- Helper for Fact 2.37: every weak closure point of `s` is the unique sequential cluster point of
some sequence in `s`. -/
private theorem exists_sequence_with_unique_cluster_of_mem_closure
    {s : Set (WeakSpace ℝ H)} {x : WeakSpace ℝ H} (hx : x ∈ closure s) :
    ∃ u : ℕ → WeakSpace ℝ H,
      (∀ n, u n ∈ s) ∧
      ∀ y : WeakSpace ℝ H,
        (∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 y)) → y = x := by
  classical
  let x0 : H := (toWeakSpace ℝ H).symm x
  let P : ℕ × WeakSpace ℝ H → Prop := fun p ↦ p.2 ∈ s
  let r : (ℕ × WeakSpace ℝ H) → (ℕ × WeakSpace ℝ H) → Prop := fun p q ↦
    p.1 < q.1 ∧
      |inner ℝ ((toWeakSpace ℝ H).symm q.2 - x0) x0| < 1 / ((q.1 : ℝ) + 1) ∧
      |inner ℝ ((toWeakSpace ℝ H).symm q.2 - x0) ((toWeakSpace ℝ H).symm p.2)| <
        1 / ((q.1 : ℝ) + 1)
  have hstep : ∀ F : Finset (ℕ × WeakSpace ℝ H), (∀ p ∈ F, P p) → ∃ q, P q ∧ ∀ p ∈ F, r p q := by
    intro F hF
    let N : ℕ := F.sup Prod.fst + 1
    let G : Finset H := insert x0 (F.image fun p ↦ (toWeakSpace ℝ H).symm p.2)
    have htube :
        {w : WeakSpace ℝ H |
            ∀ v ∈ G, |inner ℝ ((toWeakSpace ℝ H).symm w - x0) v| < 1 / ((N : ℝ) + 1)} ∈ 𝓝 x := by
      have hpos : 0 < 1 / ((N : ℝ) + 1) := by positivity
      simpa [x0, G] using weak_coordinate_tube_mem_nhds (H := H) x G hpos
    obtain ⟨z, hz_tube⟩ := (mem_closure_iff_nhds').1 hx _ htube
    refine ⟨(N, z), z.2, ?_⟩
    intro p hp
    have hp_lt : p.1 < N := by
      exact lt_of_le_of_lt (Finset.le_sup hp) (Nat.lt_succ_self _)
    have hx_mem_G : x0 ∈ G := by
      simp [G]
    have hp_mem_G : (toWeakSpace ℝ H).symm p.2 ∈ G := by
      rw [show G = insert x0 (F.image fun q ↦ (toWeakSpace ℝ H).symm q.2) by rfl]
      rw [Finset.mem_insert]
      right
      exact Finset.mem_image.2 ⟨p, hp, rfl⟩
    exact ⟨hp_lt, hz_tube _ hx_mem_G, hz_tube _ hp_mem_G⟩
  obtain ⟨f, hf_mem, hf_rel⟩ := exists_seq_of_forall_finset_exists P r hstep
  let u : ℕ → WeakSpace ℝ H := fun n ↦ (f n).2
  have hu_mem : ∀ n, u n ∈ s := by
    intro n
    exact hf_mem n
  have hindex_mono : StrictMono fun n ↦ (f n).1 := by
    intro m n hmn
    exact (hf_rel m n hmn).1
  refine ⟨u, hu_mem, ?_⟩
  intro y hy
  rcases hy with ⟨φ, hφ, hφ_tendsto⟩
  let K : Submodule ℝ H :=
    Submodule.topologicalClosure
      (Submodule.span ℝ (Set.insert x0 (Set.range fun n ↦ (toWeakSpace ℝ H).symm (u n))))
  letI : CompleteSpace ↥K := by
    change CompleteSpace ↥((Submodule.span ℝ
      (Set.insert x0 (Set.range fun n ↦ (toWeakSpace ℝ H).symm (u n)))).topologicalClosure)
    infer_instance
  have hx_mem_K : x0 ∈ K := by
    have hx_mem :
        x0 ∈ Set.insert x0 (Set.range fun n ↦ (toWeakSpace ℝ H).symm (u n)) := by
      exact Set.mem_insert _ _
    exact Submodule.closure_subset_topologicalClosure_span (R := ℝ)
      (s := Set.insert x0 (Set.range fun n ↦ (toWeakSpace ℝ H).symm (u n)))
      (subset_closure hx_mem)
  have hu_mem_K : ∀ n, (toWeakSpace ℝ H).symm (u n) ∈ K := by
    intro n
    have hu_mem_range :
        (toWeakSpace ℝ H).symm (u n) ∈
          Set.insert x0 (Set.range fun m ↦ (toWeakSpace ℝ H).symm (u m)) := by
      exact Set.mem_insert_of_mem _ (Set.mem_range_self n)
    exact Submodule.closure_subset_topologicalClosure_span (R := ℝ)
      (s := Set.insert x0 (Set.range fun n ↦ (toWeakSpace ℝ H).symm (u n)))
      (subset_closure hu_mem_range)
  let F : WeakSpace ℝ H → WeakSpace ℝ H :=
    fun z ↦ WeakSpace.map K.subtypeL (WeakSpace.map K.orthogonalProjection z)
  have hF_cont : Continuous F :=
    (WeakSpace.map K.subtypeL).continuous.comp (WeakSpace.map K.orthogonalProjection).continuous
  have hF_subseq_eq : F ∘ (u ∘ φ) = u ∘ φ := by
    funext n
    dsimp [F, u, Function.comp]
    exact weak_subtype_projection_eq_self_of_mem (K := K) (hz := hu_mem_K (φ n))
  have hFy_eq_y : F y = y := by
    -- Sequential cluster points of the constructed sequence stay in the closed span generated by
    -- `x` and the sequence itself.
    have hFy_tendsto : Tendsto (F ∘ (u ∘ φ)) atTop (𝓝 (F y)) := by
      exact (hF_cont.tendsto y).comp hφ_tendsto
    rw [hF_subseq_eq] at hFy_tendsto
    exact tendsto_nhds_unique hFy_tendsto hφ_tendsto
  have hy_mem_K : (toWeakSpace ℝ H).symm y ∈ K :=
    mem_of_weak_subtype_projection_eq_self (K := K) (hz := hFy_eq_y)
  have hindex_tendsto : Tendsto (fun n ↦ (f (φ n)).1) atTop atTop :=
    (hindex_mono.comp hφ).tendsto_atTop
  have hbound_tendsto :
      Tendsto (fun n ↦ 1 / (((f (φ n)).1 : ℝ) + 1)) atTop (𝓝 0) := by
    have hbase : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [Function.comp] using hbase.comp hindex_tendsto
  have hx_coord :
      inner ℝ ((toWeakSpace ℝ H).symm y - x0) x0 = 0 := by
    -- The stagewise `x`-coordinate control forces the subsequential limit to match `x` on `x`.
    have hcoord_tendsto :
        Tendsto (fun n ↦ inner ℝ ((toWeakSpace ℝ H).symm (u (φ n)) - x0) x0) atTop
          (𝓝 (inner ℝ ((toWeakSpace ℝ H).symm y - x0) x0)) := by
      let g : WeakSpace ℝ H → ℝ := fun z ↦ inner ℝ ((toWeakSpace ℝ H).symm z - x0) x0
      have hg : Continuous g := by
        have hcoord : Continuous fun z : WeakSpace ℝ H ↦ inner ℝ ((toWeakSpace ℝ H).symm z) x0 :=
          weakSpace_continuous_inner_right (H := H) x0
        simpa [g, inner_sub_left] using hcoord.sub continuous_const
      simpa [g] using (hg.tendsto y).comp hφ_tendsto
    have hbound :
        ∀ᶠ n in atTop,
          |inner ℝ ((toWeakSpace ℝ H).symm (u (φ n)) - x0) x0| ≤
            1 / (((f (φ n)).1 : ℝ) + 1) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hlt : 0 < φ n := lt_of_lt_of_le Nat.zero_lt_one <|
        le_trans hn (StrictMono.id_le hφ n)
      exact le_of_lt (hf_rel 0 (φ n) hlt).2.1
    have hzero_tendsto :
        Tendsto (fun n ↦ inner ℝ ((toWeakSpace ℝ H).symm (u (φ n)) - x0) x0) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      exact squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) hbound hbound_tendsto
    exact tendsto_nhds_unique hcoord_tendsto hzero_tendsto
  have hu_coord :
      ∀ m : ℕ, inner ℝ ((toWeakSpace ℝ H).symm y - x0) ((toWeakSpace ℝ H).symm (u m)) = 0 := by
    intro m
    -- The same control works for each previously chosen term `u m`.
    have hcoord_tendsto :
        Tendsto (fun n ↦
            inner ℝ ((toWeakSpace ℝ H).symm (u (φ n)) - x0) ((toWeakSpace ℝ H).symm (u m))) atTop
          (𝓝 (inner ℝ ((toWeakSpace ℝ H).symm y - x0) ((toWeakSpace ℝ H).symm (u m)))) := by
      let g : WeakSpace ℝ H → ℝ :=
        fun z ↦ inner ℝ ((toWeakSpace ℝ H).symm z - x0) ((toWeakSpace ℝ H).symm (u m))
      have hg : Continuous g := by
        have hcoord : Continuous fun z : WeakSpace ℝ H ↦
            inner ℝ ((toWeakSpace ℝ H).symm z) ((toWeakSpace ℝ H).symm (u m)) :=
          weakSpace_continuous_inner_right (H := H) ((toWeakSpace ℝ H).symm (u m))
        simpa [g, inner_sub_left] using hcoord.sub continuous_const
      simpa [g] using (hg.tendsto y).comp hφ_tendsto
    have hbound :
        ∀ᶠ n in atTop,
          |inner ℝ ((toWeakSpace ℝ H).symm (u (φ n)) - x0) ((toWeakSpace ℝ H).symm (u m))| ≤
            1 / (((f (φ n)).1 : ℝ) + 1) := by
      filter_upwards [eventually_ge_atTop (m + 1)] with n hn
      have hlt : m < φ n := lt_of_lt_of_le (Nat.lt_succ_self m) <|
        le_trans hn (StrictMono.id_le hφ n)
      exact le_of_lt (hf_rel m (φ n) hlt).2.2
    have hzero_tendsto :
        Tendsto (fun n ↦
            inner ℝ ((toWeakSpace ℝ H).symm (u (φ n)) - x0) ((toWeakSpace ℝ H).symm (u m))) atTop
          (𝓝 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      exact squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) hbound hbound_tendsto
    exact tendsto_nhds_unique hcoord_tendsto hzero_tendsto
  let L : H →L[ℝ] ℝ := InnerProductSpace.toDual ℝ H ((toWeakSpace ℝ H).symm y - x0)
  have hspan_le_ker :
      Submodule.span ℝ (Set.insert x0 (Set.range fun n ↦ (toWeakSpace ℝ H).symm (u n))) ≤ L.ker := by
    refine Submodule.span_le.2 ?_
    intro z hz
    change inner ℝ ((toWeakSpace ℝ H).symm y - x0) z = 0
    rcases hz with rfl | hz
    · exact hx_coord
    · rcases hz with ⟨n, rfl⟩
      exact hu_coord n
  have hK_le_ker : K ≤ L.ker :=
    Submodule.topologicalClosure_minimal
      (s := Submodule.span ℝ (Set.insert x0 (Set.range fun n ↦ (toWeakSpace ℝ H).symm (u n))))
      hspan_le_ker (ContinuousLinearMap.isClosed_ker L)
  have hdiff_mem : (toWeakSpace ℝ H).symm y - x0 ∈ K := K.sub_mem hy_mem_K hx_mem_K
  have hdiff_zero :
      inner ℝ ((toWeakSpace ℝ H).symm y - x0) ((toWeakSpace ℝ H).symm y - x0) = 0 :=
    hK_le_ker hdiff_mem
  have hnorm_zero : ‖(toWeakSpace ℝ H).symm y - x0‖ = 0 := by
    have hsq :
        ‖(toWeakSpace ℝ H).symm y - x0‖ ^ 2 = 0 := by
      simpa [real_inner_self_eq_norm_sq] using hdiff_zero
    nlinarith [sq_nonneg ‖(toWeakSpace ℝ H).symm y - x0‖, hsq]
  have hy_eq_x0 : (toWeakSpace ℝ H).symm y = x0 := by
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)
  exact (toWeakSpace ℝ H).injective (by simpa [x0, hy_eq_x0])

/-- Helper for Fact 2.37: a sequence in a weakly compact subset of `WeakSpace ℝ H` has a weakly
convergent subsequence after reducing to the separable closed span of its range. -/
private theorem compact_weak_subset_subseq_of_sequence_range_in_separable_span
    {s : Set (WeakSpace ℝ H)} (hs : IsCompact s)
    {x : ℕ → WeakSpace ℝ H} (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) := by
  let U : Submodule ℝ H :=
    Submodule.span ℝ (Set.range fun n ↦ (toWeakSpace ℝ H).symm (x n))
  let K : Submodule ℝ H := U.topologicalClosure
  have hK_complete : CompleteSpace ↥K := by
    change CompleteSpace ↥(U.topologicalClosure)
    infer_instance
  have hK_sep : SeparableSpace ↥K :=
    separableSpace_topologicalClosure_span_range (fun n ↦ (toWeakSpace ℝ H).symm (x n))
  let y : ℕ → WeakSpace ℝ K := fun n ↦ WeakSpace.map K.orthogonalProjection (x n)
  have hy_mem : ∀ n, y n ∈ WeakSpace.map K.orthogonalProjection '' s := by
    -- The projected sequence still lies in the projected compact set.
    intro n
    exact ⟨x n, hx n, rfl⟩
  have hs_proj : IsCompact (WeakSpace.map K.orthogonalProjection '' s) := by
    -- Orthogonal projection is weak-to-weak continuous, so it preserves compactness.
    exact hs.image (WeakSpace.map K.orthogonalProjection).continuous
  rcases
      (@compact_weak_subset_tendsto_subseq_of_separable (↥K) _ _ hK_complete hK_sep
        (WeakSpace.map K.orthogonalProjection '' s) hs_proj y hy_mem) with
      ⟨aK, haK, φ, hφ, hyφ_tendsto⟩
  let a : WeakSpace ℝ H := WeakSpace.map K.subtypeL aK
  have hx_mem_K : ∀ n, (toWeakSpace ℝ H).symm (x n) ∈ K := by
    -- Each term belongs to the closed span generated by the whole sequence range.
    intro n
    exact Submodule.closure_subset_topologicalClosure_span (R := ℝ)
      (s := Set.range fun n ↦ (toWeakSpace ℝ H).symm (x n))
      (subset_closure (Set.mem_range_self n))
  have hxφ_tendsto : Tendsto (x ∘ φ) atTop (𝓝 a) := by
    -- Re-embed the projected subsequence; on the closed span this recovers the original terms.
    have ha_tendsto :
        Tendsto (fun n ↦ WeakSpace.map K.subtypeL (y (φ n))) atTop (𝓝 a) := by
      simpa [a, y, Function.comp] using
        ((WeakSpace.map K.subtypeL).continuous.tendsto aK).comp hyφ_tendsto
    have hsubseq_eq :
        (fun n ↦ WeakSpace.map K.subtypeL (y (φ n))) = x ∘ φ := by
      funext n
      dsimp [y]
      exact weak_subtype_projection_eq_self_of_mem (K := K) (hz := hx_mem_K (φ n))
    rw [hsubseq_eq] at ha_tendsto
    exact ha_tendsto
  have ha_mem : a ∈ s := by
    -- Compact subsets of the Hausdorff weak space are closed, so the subsequence limit stays in `s`.
    exact hs.isClosed.mem_of_tendsto hxφ_tendsto (Eventually.of_forall fun n ↦ hx (φ n))
  exact ⟨a, ha_mem, φ, hφ, hxφ_tendsto⟩

-- Proof sketch: this is the Eberlein-Smulian theorem specialized to the canonical weak-topology
-- space `WeakSpace ℝ H`.
private theorem isCompact_iff_isSeqCompact_weakSpace (s : Set (WeakSpace ℝ H)) :
    IsCompact s ↔ IsSeqCompact s := by
  constructor
  · intro hs
    -- Route correction: instead of working with an arbitrary subnet, project the compact weak set
    -- to the separable closed span of the given sequence and extract a subsequence there.
    intro x hx
    exact compact_weak_subset_subseq_of_sequence_range_in_separable_span hs hx
  · intro hs
    have hb : Bornology.IsBounded ((toWeakSpace ℝ H).symm '' s) :=
      isBounded_preimage_of_isSeqCompact_weakSpace hs
    have hs_closed : IsClosed s := by
      -- Route correction: instead of proving a direct Fréchet-Urysohn statement for arbitrary
      -- weakly compact sets, build a sequence in `s` whose only weak sequential cluster point is
      -- the given closure point.
      rw [← closure_subset_iff_isClosed]
      intro x hx
      rcases exists_sequence_with_unique_cluster_of_mem_closure (H := H) hx with
        ⟨u, hu_mem, hunique⟩
      rcases hs hu_mem with ⟨y, hy, φ, hφ, hφ_tendsto⟩
      have hy_eq_x : y = x := hunique y ⟨φ, hφ, hφ_tendsto⟩
      simpa [hy_eq_x] using hy
    have himage :
        (toWeakSpace ℝ H) '' ((toWeakSpace ℝ H).symm '' s) = s := by
      ext z
      constructor
      · rintro ⟨v, ⟨w, hw, rfl⟩, rfl⟩
        exact hw
      · intro hz
        exact ⟨(toWeakSpace ℝ H).symm z, ⟨z, hz, rfl⟩, by simp⟩
    have hclosed_preimage :
        IsClosed ((toWeakSpace ℝ H) '' ((toWeakSpace ℝ H).symm '' s)) := by
      simpa [himage] using hs_closed
    have hcompact_preimage :
        IsCompact ((toWeakSpace ℝ H) '' ((toWeakSpace ℝ H).symm '' s)) :=
      (weaklyCompact_iff_weaklyClosed_and_bounded
        (C := (toWeakSpace ℝ H).symm '' s)).2 ⟨hclosed_preimage, hb⟩
    simpa [himage] using hcompact_preimage

-- Proof sketch: apply the canonical weak-space theorem to the image of `C` under `toWeakSpace`.
/-- Fact 2.37: a subset `C` of a real Hilbert space is weakly compact if and only if it is weakly
sequentially compact. -/
theorem weaklyCompact_iff_weaklySeqCompact (C : Set H) :
    IsCompact (toWeakSpace ℝ H '' C) ↔ IsSeqCompact (toWeakSpace ℝ H '' C) := by
  simpa using isCompact_iff_isSeqCompact_weakSpace ((toWeakSpace ℝ H) '' C)

end

/-! Source item: Chap02/Crollary_2_38 -/

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

/-- Corollary 2.38: for a subset `C` of a real Hilbert space, weak compactness, weak sequential
compactness, and weak closedness together with norm-boundedness are equivalent. The weak-topology
conditions are expressed by viewing `C` inside `WeakSpace ℝ 𝓗`. -/
-- Proof sketch: combine the weak compactness versus weak sequential compactness equivalence from
-- the Eberlein-Smulian theorem with the weak compactness versus weak closed and bounded
-- characterization in Hilbert spaces, and then package the resulting cycle as a `TFAE`.
theorem weaklyCompact_weaklySeqCompact_weaklyClosed_bounded_tfae (C : Set 𝓗) :
    List.TFAE
      [IsCompact ((toWeakSpace ℝ 𝓗) '' C),
        IsSeqCompact ((toWeakSpace ℝ 𝓗) '' C),
        IsClosed ((toWeakSpace ℝ 𝓗) '' C) ∧ Bornology.IsBounded C] := by
  -- Package the two canonical equivalences against weak compactness into the three-way `TFAE`.
  tfae_have 1 ↔ 2 := by
    exact weaklyCompact_iff_weaklySeqCompact C
  tfae_have 1 ↔ 3 := by
    exact weaklyCompact_iff_weaklyClosed_and_bounded
  tfae_finish

/-! Source item: Chap02/Lemma_2_39 -/

/-- Helper for Lemma 2.39: every scaled closed unit ball is weakly sequentially compact in a real
Hilbert space. -/
private lemma isSeqCompact_weakImage_smul_unit_ball
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    (a : ℝ) :
    IsSeqCompact ((toWeakSpace ℝ 𝓗) '' (a • {x : 𝓗 | ‖x‖ ≤ 1})) := by
  have hweakCompact :
      IsCompact ((toWeakSpace ℝ 𝓗) '' (a • {x : 𝓗 | ‖x‖ ≤ 1})) :=
    isCompact_weakImage_smul_unit_ball a
  -- Fact 2.37 converts weak compactness of the scaled ball into weak sequential compactness.
  exact (weaklyCompact_iff_weaklySeqCompact (a • {x : 𝓗 | ‖x‖ ≤ 1})).mp hweakCompact

/-- Lemma 2.39: for a norm-bounded subset of a real Hilbert space, weak closedness is equivalent to
weak sequential closedness. Both notions are expressed on the image of `C` in `WeakSpace ℝ 𝓗`. -/
-- Proof sketch: the forward implication is the general fact that closed subsets are sequentially
-- closed. For the converse, place `C` inside a closed ball using boundedness, use weak sequential
-- compactness of that ball and sequential closedness of `C` to get weak sequential compactness of
-- `C`, then apply weak Eberlein-Smulian to obtain weak compactness and finally use Hausdorffness of
-- `WeakSpace ℝ 𝓗` to conclude weak closedness.
theorem weaklyClosed_iff_weaklySeqClosed_of_bounded
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    {C : Set 𝓗} (hC : Bornology.IsBounded C) :
    IsClosed ((toWeakSpace ℝ 𝓗) '' C) ↔ IsSeqClosed ((toWeakSpace ℝ 𝓗) '' C) := by
  constructor
  · intro hclosed
    -- Closed subsets are sequentially closed in every topological space.
    exact hclosed.isSeqClosed
  · intro hseqClosed
    have hclosedBall :
        (Metric.closedBall (0 : 𝓗) 1 : Set 𝓗) = {x : 𝓗 | ‖x‖ ≤ 1} := by
      ext x
      simp [Metric.mem_closedBall, dist_eq_norm]
    rcases (NormedSpace.isBounded_iff_subset_smul_closedBall ℝ).1 hC with ⟨a, ha⟩
    have hsubset :
        C ⊆ a • {x : 𝓗 | ‖x‖ ≤ 1} := by
      simpa [hclosedBall] using ha
    have hsubsetWeak :
        (toWeakSpace ℝ 𝓗) '' C ⊆ (toWeakSpace ℝ 𝓗) '' (a • {x : 𝓗 | ‖x‖ ≤ 1}) := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, hsubset hx, rfl⟩
    have hseqCompactAmbient :
        IsSeqCompact ((toWeakSpace ℝ 𝓗) '' (a • {x : 𝓗 | ‖x‖ ≤ 1})) :=
      isSeqCompact_weakImage_smul_unit_ball a
    have hseqCompactC : IsSeqCompact ((toWeakSpace ℝ 𝓗) '' C) :=
      hseqCompactAmbient.of_isSeqClosed_subset hseqClosed hsubsetWeak
    have hcompactC : IsCompact ((toWeakSpace ℝ 𝓗) '' C) :=
      (weaklyCompact_iff_weaklySeqCompact C).mpr hseqCompactC
    have hcompact_iff :
        IsCompact ((toWeakSpace ℝ 𝓗) '' C) ↔
          IsClosed ((toWeakSpace ℝ 𝓗) '' C) ∧ Bornology.IsBounded C :=
      weaklyCompact_iff_weaklyClosed_and_bounded
    exact (hcompact_iff.mp hcompactC).1

/-! Source item: Chap02/Remark_2_31 -/

variable {A : Type v} [Preorder A] [IsDirectedOrder A]
variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

omit [IsDirectedOrder A] in
private theorem weakConvergence_iff_forall_tendsto_inner_right_aux
    [CompleteSpace 𝓗] (ξ : A → 𝓗) (x : 𝓗) :
    Tendsto (fun a ↦ toWeakSpace ℝ 𝓗 (ξ a)) atTop (𝓝 (toWeakSpace ℝ 𝓗 x)) ↔
      ∀ u : 𝓗, Tendsto (fun a ↦ ⟪ξ a, u⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) := by
  have hinj : Function.Injective ((topDualPairing ℝ 𝓗).flip) := by
    intro y z hyz
    exact (SeparatingDual.eq_iff_forall_dual_eq).2 fun l ↦ DFunLike.congr_fun hyz l
  constructor
  · intro hξ u
    exact ((weakSpace_continuous_inner_right u).tendsto (toWeakSpace ℝ 𝓗 x)).comp hξ
  · intro hξ
    refine (WeakBilin.tendsto_iff_forall_eval_tendsto ((topDualPairing ℝ 𝓗).flip) hinj).2 ?_
    intro l
    let u : 𝓗 := (InnerProductSpace.toDual ℝ 𝓗).symm (WeakDual.toStrongDual l)
    have hu : Tendsto (fun a ↦ ⟪ξ a, u⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) := hξ u
    have hξeq : ∀ a, l (toWeakSpace ℝ 𝓗 (ξ a)) = ⟪ξ a, u⟫_ℝ := by
      intro a
      change WeakDual.toStrongDual l (ξ a) = _
      rw [← InnerProductSpace.toDual_symm_apply, real_inner_comm]
    have hxeq : l (toWeakSpace ℝ 𝓗 x) = ⟪x, u⟫_ℝ := by
      change WeakDual.toStrongDual l x = _
      rw [← InnerProductSpace.toDual_symm_apply, real_inner_comm]
    change Tendsto (fun a ↦ l (toWeakSpace ℝ 𝓗 (ξ a))) atTop (𝓝 (l (toWeakSpace ℝ 𝓗 x)))
    rw [show (fun a ↦ l (toWeakSpace ℝ 𝓗 (ξ a))) = fun a ↦ ⟪ξ a, u⟫_ℝ by
      funext a
      exact hξeq a]
    rw [hxeq]
    exact hu

omit [IsDirectedOrder A] in
private theorem tendsto_infDist_hyperplane_iff_tendsto_inner_right
    (ξ : A → 𝓗) (x u : 𝓗) (hu : u ≠ 0) :
    Tendsto (fun a ↦ Metric.infDist (ξ a) (innerProductLevelSet u ⟪x, u⟫_ℝ)) atTop (𝓝 0) ↔
      Tendsto (fun a ↦ ⟪ξ a, u⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) := by
  constructor
  · intro hdist
    have hdist' : Tendsto
        (fun a ↦ |⟪ξ a, u⟫_ℝ - ⟪x, u⟫_ℝ| / ‖u‖) atTop (𝓝 0) := by
      simpa [infDist_hyperplane_eq_abs_inner_sub_div_norm, hu] using hdist
    have hnorm : Tendsto (fun a ↦ ‖⟪ξ a, u⟫_ℝ - ⟪x, u⟫_ℝ‖) atTop (𝓝 0) := by
      have hmul :=
        hdist'.mul (tendsto_const_nhds : Tendsto (fun _ : A ↦ ‖u‖) atTop (𝓝 ‖u‖))
      simpa [Real.norm_eq_abs, div_mul_cancel₀ _ (show ‖u‖ ≠ 0 by simpa using hu)] using hmul
    have hsub : Tendsto (fun a ↦ ⟪ξ a, u⟫_ℝ - ⟪x, u⟫_ℝ) atTop (𝓝 0) :=
      (tendsto_zero_iff_norm_tendsto_zero).2 hnorm
    simpa using
      hsub.add (tendsto_const_nhds : Tendsto (fun _ : A ↦ ⟪x, u⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ))
  · intro hξ
    have hsub : Tendsto (fun a ↦ ⟪ξ a, u⟫_ℝ - ⟪x, u⟫_ℝ) atTop (𝓝 0) := by
      simpa [sub_eq_add_neg] using
        hξ.add (tendsto_const_nhds : Tendsto (fun _ : A ↦ -⟪x, u⟫_ℝ) atTop (𝓝 (-⟪x, u⟫_ℝ)))
    have hnorm : Tendsto (fun a ↦ ‖⟪ξ a, u⟫_ℝ - ⟪x, u⟫_ℝ‖) atTop (𝓝 0) := by
      simpa using hsub.norm
    have hdist' : Tendsto
        (fun a ↦ ‖u‖⁻¹ * ‖⟪ξ a, u⟫_ℝ - ⟪x, u⟫_ℝ‖) atTop (𝓝 0) := by
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : A ↦ ‖u‖⁻¹) atTop (𝓝 ‖u‖⁻¹)).mul hnorm
    simpa [infDist_hyperplane_eq_abs_inner_sub_div_norm, hu, Real.norm_eq_abs,
      div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdist'

omit [IsDirectedOrder A] [InnerProductSpace ℝ 𝓗] in
/-- Remark 2.31 (1): strong convergence of a net to `x` is equivalent to the distance
`dist (ξ a) x` tending to `0`. -/
theorem strongConvergence_iff_tendsto_dist (ξ : A → 𝓗) (x : 𝓗) :
    Tendsto ξ atTop (𝓝 x) ↔ Tendsto (fun a ↦ dist (ξ a) x) atTop (𝓝 0) := by
  simpa using (tendsto_iff_dist_tendsto_zero : Tendsto ξ atTop (𝓝 x) ↔ _)

omit [IsDirectedOrder A] [InnerProductSpace ℝ 𝓗] in
/-- Remark 2.31 (1): strong convergence of a net to `x` is equivalent to convergence to `0` of the
distance from the net to the singleton `{x}`. -/
theorem strongConvergence_iff_tendsto_infDist_singleton (ξ : A → 𝓗) (x : 𝓗) :
    Tendsto ξ atTop (𝓝 x) ↔
      Tendsto (fun a ↦ Metric.infDist (ξ a) ({x} : Set 𝓗)) atTop (𝓝 0) := by
  simpa [Metric.infDist_singleton] using strongConvergence_iff_tendsto_dist ξ x

omit [IsDirectedOrder A] in
/-- A net converges weakly to `x` exactly when all scalar inner-product coordinates against fixed
vectors converge to the corresponding coordinate of `x`. -/
theorem weakConvergence_iff_forall_tendsto_inner_right
    [CompleteSpace 𝓗] (ξ : A → 𝓗) (x : 𝓗) :
    Tendsto (fun a ↦ toWeakSpace ℝ 𝓗 (ξ a)) atTop (𝓝 (toWeakSpace ℝ 𝓗 x)) ↔
      ∀ u : 𝓗, Tendsto (fun a ↦ ⟪ξ a, u⟫_ℝ) atTop (𝓝 ⟪x, u⟫_ℝ) :=
  weakConvergence_iff_forall_tendsto_inner_right_aux ξ x

omit [IsDirectedOrder A] in
/-- Remark 2.31 (2): weak convergence of a net to `x` is equivalent to convergence to `0` of the
distance to every closed hyperplane through `x`, encoded as
`innerProductLevelSet u ⟪x, u⟫_ℝ` with `u ≠ 0`. -/
theorem weakConvergence_iff_forall_tendsto_infDist_hyperplane
    [CompleteSpace 𝓗] (ξ : A → 𝓗) (x : 𝓗) :
    Tendsto (fun a ↦ toWeakSpace ℝ 𝓗 (ξ a)) atTop (𝓝 (toWeakSpace ℝ 𝓗 x)) ↔
      ∀ u : 𝓗, u ≠ 0 →
        Tendsto (fun a ↦ Metric.infDist (ξ a) (innerProductLevelSet u ⟪x, u⟫_ℝ)) atTop (𝓝 0) := by
  rw [weakConvergence_iff_forall_tendsto_inner_right]
  constructor
  · intro hξ u hu
    exact (tendsto_infDist_hyperplane_iff_tendsto_inner_right ξ x u hu).2 (hξ u)
  · intro hξ u
    by_cases hu : u = 0
    · simpa [hu] using (tendsto_const_nhds : Tendsto (fun _ : A ↦ (0 : ℝ)) atTop (𝓝 0))
    · exact (tendsto_infDist_hyperplane_iff_tendsto_inner_right ξ x u hu).1 (hξ u hu)
