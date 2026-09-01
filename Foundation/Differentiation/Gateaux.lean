import Mathlib

/-!
# Differentiation Gateaux

Gateaux and Frechet differentiability, gradients, second derivatives, and quadratic or least-squares examples.
-/

open scoped Topology
open InnerProductSpace
open scoped InnerProductSpace
open ContinuousLinearMap
open scoped Gradient InnerProductSpace
open Filter
open scoped InnerProductSpace Gradient Topology
open MeasureTheory

/-! Source item: Chap02/Definition_2_54 -/
universe u v


variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- A set `C` admits short positive line segments from `x` in every direction. -/
def HasRadialSegmentsAt (C : Set H) (x : H) : Prop :=
  ∀ y : H, ∃ α : ℝ, 0 < α ∧ ∀ t ∈ Set.Icc (0 : ℝ) α, x + t • y ∈ C

/-- Definition 2.54: `A` is the Gâteaux derivative of `T` at `x` within `C` if every direction
from `x` stays in `C` along some short positive segment and the restriction of `T` to each affine
line through `x` has the one-sided derivative `A y` at `0`. -/
def HasGateauxDerivativeWithinAt (T : H → K) (A : H →L[ℝ] K) (C : Set H) (x : H) : Prop :=
  HasRadialSegmentsAt C x ∧
    ∀ y : H,
      HasDerivWithinAt (fun α : ℝ ↦ T (x + α • y)) (A y) (Set.Ioi 0) 0

/-- `T` has Gâteaux derivative `A` at `x` if it has this derivative within the whole space. -/
abbrev HasGateauxDerivativeAt (T : H → K) (A : H →L[ℝ] K) (x : H) : Prop :=
  HasGateauxDerivativeWithinAt T A Set.univ x

/-- `T` is Gâteaux differentiable within `C` at `x` if it admits some Gâteaux derivative there. -/
abbrev GateauxDifferentiableWithinAt (T : H → K) (C : Set H) (x : H) : Prop :=
  ∃ A : H →L[ℝ] K, HasGateauxDerivativeWithinAt T A C x

/-- `T` is Gâteaux differentiable at `x` if it is Gâteaux differentiable within the whole space. -/
abbrev GateauxDifferentiableAt (T : H → K) (x : H) : Prop :=
  ∃ A : H →L[ℝ] K, HasGateauxDerivativeAt T A x

/-- `T` is Gâteaux differentiable on `C` if it is Gâteaux differentiable at every point of `C`. -/
def GateauxDifferentiableOn (T : H → K) (C : Set H) : Prop :=
  ∀ x ∈ C, GateauxDifferentiableWithinAt T C x

/-- A derivative field `DT` on `C` assigns to each point of `C` a Gâteaux derivative of `T`. -/
def HasGateauxDerivativeOn (T : H → K) (DT : H → H →L[ℝ] K) (C : Set H) : Prop :=
  ∀ x ∈ C, HasGateauxDerivativeWithinAt T (DT x) C x

/-- Definition 2.54: relative to a first-derivative field `DT`, `A₂` is a second Gâteaux
derivative of `T` at `x` within `C` if `DT x` is a Gâteaux derivative of `T` at `x` within `C`
and the operator field `DT` has Gâteaux derivative `A₂` there. -/
def HasGateauxSecondDerivativeWithinAt
    (T : H → K) (DT : H → H →L[ℝ] K) (C : Set H)
    (x : H) (A₂ : H →L[ℝ] (H →L[ℝ] K)) : Prop :=
  HasGateauxDerivativeWithinAt T (DT x) C x ∧ HasGateauxDerivativeWithinAt DT A₂ C x

/-- A neighborhood of `x` contains a short positive line segment from `x` in every direction. -/
theorem HasRadialSegmentsAt.of_mem_nhds
    {C : Set H} {x : H} (hC : C ∈ 𝓝 x) :
    HasRadialSegmentsAt C x := by
  intro y
  rcases Metric.mem_nhds_iff.1 hC with ⟨r, hrpos, hrC⟩
  refine ⟨r / (‖y‖ + 1), by positivity, ?_⟩
  intro t ht
  apply hrC
  have ht_nonneg : 0 ≤ t := ht.1
  have hy_pos : 0 < ‖y‖ + 1 := by positivity
  calc
    dist (x + t • y) x = ‖t • y‖ := by
      simp [dist_eq_norm, sub_eq_add_neg, add_assoc]
    _ = ‖t‖ * ‖y‖ := norm_smul t y
    _ = t * ‖y‖ := by rw [Real.norm_of_nonneg ht_nonneg]
    _ ≤ (r / (‖y‖ + 1)) * ‖y‖ := by nlinarith [ht.2, norm_nonneg y]
    _ < (r / (‖y‖ + 1)) * (‖y‖ + 1) := by
      gcongr
      linarith [norm_nonneg y]
    _ = r := by field_simp [hy_pos.ne']

/-- Helper for Definition 2.54: the whole space admits radial segments at every point. -/
theorem hasRadialSegmentsAt_univ (x : H) : HasRadialSegmentsAt (Set.univ : Set H) x :=
  HasRadialSegmentsAt.of_mem_nhds Filter.univ_mem

/-- A Fréchet derivative within a neighborhood gives the corresponding Gâteaux derivative. -/
theorem HasFDerivWithinAt.hasGateauxDerivativeWithinAt
    {C : Set H} {T : H → K} {x : H} {A : H →L[ℝ] K}
    (hT : HasFDerivWithinAt T A C x) (hC : C ∈ 𝓝 x) :
    HasGateauxDerivativeWithinAt T A C x := by
  refine ⟨HasRadialSegmentsAt.of_mem_nhds hC, ?_⟩
  intro y
  simpa [HasLineDerivAt] using
    (((hT.hasLineDerivWithinAt y).hasLineDerivAt hC).hasDerivWithinAt :
      HasDerivWithinAt (fun α : ℝ ↦ T (x + α • y)) (A y) (Set.Ioi 0) 0)

/-- A Fréchet derivative gives the corresponding Gâteaux derivative in the whole space. -/
theorem HasFDerivAt.hasGateauxDerivativeAt
    {T : H → K} {x : H} {A : H →L[ℝ] K}
    (hT : HasFDerivAt T A x) :
    HasGateauxDerivativeAt T A x := by
  simpa [HasGateauxDerivativeAt] using
    HasFDerivWithinAt.hasGateauxDerivativeWithinAt hT.hasFDerivWithinAt Filter.univ_mem

/-- In the whole space, a Gâteaux derivative yields the corresponding line derivative in every
direction. -/
theorem hasLineDerivAt_of_hasGateauxDerivativeAt
    {T : H → K} {x : H} {A : H →L[ℝ] K}
    (hT : HasGateauxDerivativeAt T A x) (y : H) :
    HasLineDerivAt ℝ T (A y) x y := by
  let path : ℝ → K := fun t ↦ T (x + t • y)
  have hright : HasDerivWithinAt path (A y) (Set.Ioi 0) 0 := by
    simpa [HasGateauxDerivativeAt, path] using hT.2 y
  have hleftAux : HasDerivWithinAt path (A y) (Set.Iio 0) 0 := by
    let negPath : ℝ → K := fun s ↦ T (x + s • (-y))
    have hneg : HasDerivWithinAt negPath (A (-y)) (Set.Ioi 0) 0 := by
      simpa [HasGateauxDerivativeAt, negPath] using hT.2 (-y)
    have hnegTendsto :
        Filter.Tendsto (slope negPath 0) (𝓝[Set.Ioi 0] 0) (𝓝 (A (-y))) :=
      (hasDerivWithinAt_iff_tendsto_slope' (by simp)).1 hneg
    have hnegMap :
        Filter.Tendsto (fun t : ℝ ↦ -t) (𝓝[Set.Iio 0] 0) (𝓝[Set.Ioi 0] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · simpa [ContinuousWithinAt] using
          (continuous_neg.continuousAt.continuousWithinAt :
            ContinuousWithinAt (fun t : ℝ ↦ -t) (Set.Iio 0) 0)
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa [Set.mem_Iio, Set.mem_Ioi] using neg_pos.mpr (show t < 0 by simpa using ht)
    have hcomp :
        Filter.Tendsto (fun t : ℝ ↦ slope negPath 0 (-t)) (𝓝[Set.Iio 0] 0) (𝓝 (A (-y))) :=
      hnegTendsto.comp hnegMap
    have hleftTendsto :
        Filter.Tendsto (fun t : ℝ ↦ slope path 0 t) (𝓝[Set.Iio 0] 0) (𝓝 (A y)) := by
      convert hcomp.neg using 1
      · ext t
        by_cases ht : t = 0
        · simp [ht, path, negPath]
        · rw [slope_def_module, slope_def_module]
          simp [path, negPath]
      · simp
    exact (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Iio 0 by simp)).2 hleftTendsto
  rw [HasLineDerivAt, hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · exact (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Iio 0 by simp)).1 hleftAux
  · exact (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Ioi 0 by simp)).1 hright

/-- A Gâteaux derivative within `C` yields the corresponding two-sided line derivative. -/
theorem HasGateauxDerivativeWithinAt.hasLineDerivAt
    {C : Set H} {T : H → K} {x : H} {A : H →L[ℝ] K}
    (hT : HasGateauxDerivativeWithinAt T A C x) (y : H) :
    HasLineDerivAt ℝ T (A y) x y := by
  let path : ℝ → K := fun t ↦ T (x + t • y)
  have hright : HasDerivWithinAt path (A y) (Set.Ioi 0) 0 := by
    simpa [path] using hT.2 y
  have hleftAux : HasDerivWithinAt path (A y) (Set.Iio 0) 0 := by
    let negPath : ℝ → K := fun s ↦ T (x + s • (-y))
    have hneg : HasDerivWithinAt negPath (A (-y)) (Set.Ioi 0) 0 := by
      simpa [negPath] using hT.2 (-y)
    have hnegTendsto :
        Filter.Tendsto (slope negPath 0) (𝓝[Set.Ioi 0] 0) (𝓝 (A (-y))) :=
      (hasDerivWithinAt_iff_tendsto_slope' (by simp)).1 hneg
    have hnegMap :
        Filter.Tendsto (fun t : ℝ ↦ -t) (𝓝[Set.Iio 0] 0) (𝓝[Set.Ioi 0] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · simpa [ContinuousWithinAt] using
          (continuous_neg.continuousAt.continuousWithinAt :
            ContinuousWithinAt (fun t : ℝ ↦ -t) (Set.Iio 0) 0)
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa [Set.mem_Iio, Set.mem_Ioi] using neg_pos.mpr (show t < 0 by simpa using ht)
    have hcomp :
        Filter.Tendsto (fun t : ℝ ↦ slope negPath 0 (-t)) (𝓝[Set.Iio 0] 0) (𝓝 (A (-y))) :=
      hnegTendsto.comp hnegMap
    have hleftTendsto :
        Filter.Tendsto (fun t : ℝ ↦ slope path 0 t) (𝓝[Set.Iio 0] 0) (𝓝 (A y)) := by
      convert hcomp.neg using 1
      · ext t
        by_cases ht : t = 0
        · simp [ht, path, negPath]
        · rw [slope_def_module, slope_def_module]
          simp [path, negPath]
      · simp
    exact (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Iio 0 by simp)).2 hleftTendsto
  rw [HasLineDerivAt, hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · exact (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Iio 0 by simp)).1 hleftAux
  · exact (hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Set.Ioi 0 by simp)).1 hright

/-- Whole-space Gâteaux differentiability is exactly the existence of the corresponding line
derivative in every direction. -/
theorem hasGateauxDerivativeAt_iff_forall_hasLineDerivAt
    {T : H → K} {x : H} {A : H →L[ℝ] K} :
    HasGateauxDerivativeAt T A x ↔ ∀ y : H, HasLineDerivAt ℝ T (A y) x y := by
  constructor
  · intro hT y
    exact hasLineDerivAt_of_hasGateauxDerivativeAt hT y
  · intro hT
    refine ⟨hasRadialSegmentsAt_univ x, ?_⟩
    intro y
    simpa [HasLineDerivAt] using (hT y).hasDerivWithinAt

/-- Definition 2.54 in textbook form: the one-sided line-derivative formulation is equivalent to
the convergence of directional difference quotients to `A y` as the scalar tends to `0` from the
right. -/
theorem hasGateauxDerivativeWithinAt_iff_tendsto_directionalDifferenceQuotient
    {C : Set H} {T : H → K} {x : H} {A : H →L[ℝ] K} :
    HasGateauxDerivativeWithinAt T A C x ↔
      HasRadialSegmentsAt C x ∧
        ∀ y : H,
          Filter.Tendsto (fun α : ℝ ↦ (1 / α) • (T (x + α • y) - T x))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) := by
  constructor
  · rintro ⟨hSegments, hDeriv⟩
    refine ⟨hSegments, ?_⟩
    intro y
    let path : ℝ → K := fun α ↦ T (x + α • y)
    have hpath : HasDerivWithinAt path (A y) (Set.Ioi 0) 0 := hDeriv y
    have htendsto :
        Filter.Tendsto (slope path 0) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) :=
      (hasDerivWithinAt_iff_tendsto_slope' (by simp)).1 hpath
    have hslope :
        slope path 0 = fun α : ℝ ↦ (1 / α) • (T (x + α • y) - T x) := by
      ext α
      simp [path, slope_def_module, one_div]
    simpa [hslope] using htendsto
  · rintro ⟨hSegments, hTendsto⟩
    refine ⟨hSegments, ?_⟩
    intro y
    let path : ℝ → K := fun α ↦ T (x + α • y)
    have hslope :
        slope path 0 = fun α : ℝ ↦ (1 / α) • (T (x + α • y) - T x) := by
      ext α
      simp [path, slope_def_module, one_div]
    have htendsto :
        Filter.Tendsto (slope path 0) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) := by
      rw [hslope]
      exact hTendsto y
    exact (hasDerivWithinAt_iff_tendsto_slope' (by simp)).2 htendsto

/-- A Gâteaux derivative provides the textbook directional-difference-quotient limit. -/
theorem HasGateauxDerivativeWithinAt.tendsto_directionalDifferenceQuotient
    {C : Set H} {T : H → K} {x : H} {A : H →L[ℝ] K}
    (h : HasGateauxDerivativeWithinAt T A C x) :
    ∀ y : H,
      Filter.Tendsto (fun α : ℝ ↦ (1 / α) • (T (x + α • y) - T x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) :=
  (hasGateauxDerivativeWithinAt_iff_tendsto_directionalDifferenceQuotient.1 h).2

/-- Definition 2.54 in second-order form: the operator-valued line-derivative formulation for
`DT` is equivalent to the convergence of operator directional difference quotients to `A₂ y` as
the scalar tends to `0` from the right, together with the local first-derivative condition
`DT x = T'(x)`. -/
theorem hasGateauxSecondDerivativeWithinAt_iff_tendsto_directionalDifferenceQuotient
    {C : Set H} {T : H → K} {DT : H → H →L[ℝ] K} {x : H}
    {A₂ : H →L[ℝ] (H →L[ℝ] K)} :
    HasGateauxSecondDerivativeWithinAt T DT C x A₂ ↔
      HasGateauxDerivativeWithinAt T (DT x) C x ∧
        HasRadialSegmentsAt C x ∧
          ∀ y : H,
            Filter.Tendsto (fun α : ℝ ↦ (1 / α) • (DT (x + α • y) - DT x))
              (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A₂ y)) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, hasGateauxDerivativeWithinAt_iff_tendsto_directionalDifferenceQuotient.1 h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, hasGateauxDerivativeWithinAt_iff_tendsto_directionalDifferenceQuotient.2 h₂⟩

/-- A second Gâteaux derivative at `x` provides the corresponding first Gâteaux derivative there. -/
theorem HasGateauxSecondDerivativeWithinAt.hasGateauxDerivativeWithinAt
    {C : Set H} {T : H → K} {DT : H → H →L[ℝ] K} {x : H}
    {A₂ : H →L[ℝ] (H →L[ℝ] K)}
    (h : HasGateauxSecondDerivativeWithinAt T DT C x A₂) :
    HasGateauxDerivativeWithinAt T (DT x) C x :=
  h.1

/-- A second Gâteaux derivative at `x` differentiates the derivative field `DT` at `x`. -/
theorem HasGateauxSecondDerivativeWithinAt.hasGateauxDerivativeFieldWithinAt
    {C : Set H} {T : H → K} {DT : H → H →L[ℝ] K} {x : H}
    {A₂ : H →L[ℝ] (H →L[ℝ] K)}
    (h : HasGateauxSecondDerivativeWithinAt T DT C x A₂) :
    HasGateauxDerivativeWithinAt DT A₂ C x :=
  h.2

/-- A second Gâteaux derivative gives the textbook operator directional-difference-quotient limit
for the derivative field `DT`. -/
theorem HasGateauxSecondDerivativeWithinAt.tendsto_directionalDifferenceQuotient
    {C : Set H} {T : H → K} {DT : H → H →L[ℝ] K} {x : H}
    {A₂ : H →L[ℝ] (H →L[ℝ] K)}
    (h : HasGateauxSecondDerivativeWithinAt T DT C x A₂) :
    ∀ y : H,
      Filter.Tendsto (fun α : ℝ ↦ (1 / α) • (DT (x + α • y) - DT x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A₂ y)) :=
  (hasGateauxSecondDerivativeWithinAt_iff_tendsto_directionalDifferenceQuotient.1 h).2.2

/-- In the whole space, Definition 2.54 reduces to the directional-difference-quotient limit. -/
theorem hasGateauxDerivativeAt_iff_tendsto_directionalDifferenceQuotient
    {T : H → K} {x : H} {A : H →L[ℝ] K} :
    HasGateauxDerivativeAt T A x ↔
      ∀ y : H,
        Filter.Tendsto (fun α : ℝ ↦ (1 / α) • (T (x + α • y) - T x))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) := by
  have hiff :
      HasGateauxDerivativeWithinAt T A Set.univ x ↔
        HasRadialSegmentsAt (Set.univ : Set H) x ∧
          ∀ y : H,
            Filter.Tendsto (fun α : ℝ ↦ (1 / α) • (T (x + α • y) - T x))
              (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) :=
    hasGateauxDerivativeWithinAt_iff_tendsto_directionalDifferenceQuotient
  simpa [HasGateauxDerivativeAt, hasRadialSegmentsAt_univ] using hiff

/-- A Gâteaux derivative in the whole space provides the textbook directional-difference-quotient
limit. -/
theorem HasGateauxDerivativeAt.tendsto_directionalDifferenceQuotient
    {T : H → K} {x : H} {A : H →L[ℝ] K}
    (h : HasGateauxDerivativeAt T A x) :
    ∀ y : H,
      Filter.Tendsto (fun α : ℝ ↦ (1 / α) • (T (x + α • y) - T x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) :=
  hasGateauxDerivativeAt_iff_tendsto_directionalDifferenceQuotient.1 h

/-- A Gâteaux derivative at `x` forces the directional segment condition at `x`. -/
theorem HasGateauxDerivativeWithinAt.hasRadialSegmentsAt
    {C : Set H} {T : H → K} {x : H} {A : H →L[ℝ] K}
    (h : HasGateauxDerivativeWithinAt T A C x) :
    HasRadialSegmentsAt C x :=
  h.1

/-- `T` is Gâteaux differentiable within `C` at `x` exactly when it admits some Gâteaux derivative
there. -/
theorem gateauxDifferentiableWithinAt_iff_exists_hasGateauxDerivativeWithinAt
    {C : Set H} {T : H → K} {x : H} :
    GateauxDifferentiableWithinAt T C x ↔
      ∃ A : H →L[ℝ] K, HasGateauxDerivativeWithinAt T A C x :=
  Iff.rfl

/-- `T` is Gâteaux differentiable at `x` exactly when it admits some Gâteaux derivative there. -/
theorem gateauxDifferentiableAt_iff_exists_hasGateauxDerivativeAt
    {T : H → K} {x : H} :
    GateauxDifferentiableAt T x ↔ ∃ A : H →L[ℝ] K, HasGateauxDerivativeAt T A x :=
  Iff.rfl

/-! Source item: Chap02/Definition_2_56 -/
universe w


section

variable
    {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {H : Type v} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    {K : Type w} [NormedAddCommGroup K] [NormedSpace 𝕜 K]

/-- Definition 2.56: a bounded operator `T''` is a second Fréchet derivative of `T` at `x` within
`C` if it is the derivative at `x` of a first-derivative map defined on some neighborhood of `x`
contained in `C`. -/
def HasSecondFrechetDerivWithinAt
    (𝕜 : Type u) [NontriviallyNormedField 𝕜]
    {H : Type v} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    {K : Type w} [NormedAddCommGroup K] [NormedSpace 𝕜 K]
    (T : H → K) (C : Set H) (x : H) (T'' : H →L[𝕜] H →L[𝕜] K) : Prop :=
  ∃ U : Set H, U ∈ 𝓝 x ∧ U ⊆ C ∧
    ∃ T' : H → H →L[𝕜] K,
      (∀ y ∈ U, HasFDerivWithinAt T (T' y) U y) ∧
      HasFDerivWithinAt T' T'' U x

/-- Unfolding `HasSecondFrechetDerivWithinAt` amounts to the existence of a neighborhood of `x`
contained in `C` together with a first-derivative map for `T` on that neighborhood whose
derivative at `x` is `T''`. -/
theorem hasSecondFrechetDerivWithinAt_iff
    {T : H → K} {C : Set H} {x : H} {T'' : H →L[𝕜] H →L[𝕜] K} :
    HasSecondFrechetDerivWithinAt 𝕜 T C x T'' ↔
      ∃ U : Set H, U ∈ 𝓝 x ∧ U ⊆ C ∧
        ∃ T' : H → H →L[𝕜] K,
          (∀ y ∈ U, HasFDerivWithinAt T (T' y) U y) ∧
          HasFDerivWithinAt T' T'' U x :=
  Iff.rfl

/-- Being twice Fréchet differentiable at `x` within `C` means admitting some second Fréchet
derivative there. -/
def TwiceFrechetDifferentiableWithinAt
    (𝕜 : Type u) [NontriviallyNormedField 𝕜]
    {H : Type v} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
    {K : Type w} [NormedAddCommGroup K] [NormedSpace 𝕜 K]
    (T : H → K) (C : Set H) (x : H) : Prop :=
  ∃ T'' : H →L[𝕜] H →L[𝕜] K, HasSecondFrechetDerivWithinAt 𝕜 T C x T''

/-- Existence of a second Fréchet derivative is exactly twice Fréchet differentiability. -/
theorem twiceFrechetDifferentiableWithinAt_iff_exists_hasSecondFrechetDerivWithinAt
    {T : H → K} {C : Set H} {x : H} :
    TwiceFrechetDifferentiableWithinAt 𝕜 T C x ↔
      ∃ T'' : H →L[𝕜] H →L[𝕜] K, HasSecondFrechetDerivWithinAt 𝕜 T C x T'' :=
  Iff.rfl

/-- A global `C²` map is twice Fréchet differentiable on the whole space in the sense of
Definition 2.56. -/
theorem ContDiff.twiceFrechetDifferentiableWithinAt_univ
    {T : H → K} (hT : ContDiff 𝕜 2 T) (x : H) :
    TwiceFrechetDifferentiableWithinAt 𝕜 T Set.univ x := by
  have hDiff : Differentiable 𝕜 T := hT.differentiable (by norm_num)
  have hFDeriv : ContDiff 𝕜 1 (fderiv 𝕜 T) := by
    have hSucc : ContDiff 𝕜 (1 + 1) T := by
      simpa using hT
    exact (contDiff_succ_iff_fderiv.1 hSucc).2.2
  have hDiffFDeriv : Differentiable 𝕜 (fderiv 𝕜 T) := hFDeriv.differentiable_one
  refine ⟨fderiv 𝕜 (fderiv 𝕜 T) x, Set.univ, by simp, by simp, fderiv 𝕜 T, ?_, ?_⟩
  · intro y hy
    exact (hDiff y).hasFDerivAt.hasFDerivWithinAt
  · exact (hDiffFDeriv x).hasFDerivAt.hasFDerivWithinAt

end

/-! Source item: Chap02/Remark_2_55 -/

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Remark 2.55: on a real Hilbert space, the Fréchet derivative within `C` is represented by the
canonical vector `gradientWithin f C x`. -/
-- Proof sketch: use `DifferentiableWithinAt.hasGradientWithinAt`, identify the derivative with
-- `fderivWithin`, and rewrite using symmetry of the real inner product.
theorem fderivWithin_eq_inner_gradientWithin
    {C : Set H} {f : H → ℝ} {x y : H}
    (hf : DifferentiableWithinAt ℝ f C x) (hC : UniqueDiffWithinAt ℝ C x) :
    fderivWithin ℝ f C x y = ⟪y, gradientWithin f C x⟫_ℝ := by
  simpa [real_inner_comm] using (inner_gradientWithin_left hf hC).symm

/-- The Fréchet derivative within `C` has `gradientWithin f C x` as its unique Riesz
representer. -/
theorem existsUnique_gradientWithin_of_differentiableWithinAt
    {C : Set H} {f : H → ℝ} {x : H}
    (hf : DifferentiableWithinAt ℝ f C x) (hC : UniqueDiffWithinAt ℝ C x) :
    ∃! g : H, ∀ y : H, fderivWithin ℝ f C x y = ⟪y, g⟫_ℝ := by
  have hgradient : ∀ y : H, fderivWithin ℝ f C x y = ⟪y, gradientWithin f C x⟫_ℝ :=
    fun y ↦ fderivWithin_eq_inner_gradientWithin hf hC
  refine ⟨gradientWithin f C x, hgradient, ?_⟩
  intro g hg
  exact ext_inner_left ℝ fun y ↦ (hg y).symm.trans (hgradient y)

end

/-! Source item: Chap02/Example_2_57 -/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The quadratic-affine functional associated with a bounded linear operator `L` and a vector
`u`. -/
def quadratic_affine_functional (L : H →L[ℝ] H) (u : H) : H → ℝ :=
  fun y ↦ ⟪L y, y⟫_ℝ - ⟪y, u⟫_ℝ

-- Proof sketch: unfold `quadratic_affine_functional`.
/-- Evaluating `quadratic_affine_functional L u` gives its defining inner-product formula. -/
@[simp]
theorem quadratic_affine_functional_apply (L : H →L[ℝ] H) (u y : H) :
    quadratic_affine_functional L u y = ⟪L y, y⟫_ℝ - ⟪y, u⟫_ℝ := by
  -- This is exactly the definition of the quadratic-affine functional.
  rfl

-- Proof sketch: combine the explicit derivatives of the quadratic and affine terms.
/-- The quadratic-affine functional associated with `L` and `u` is twice Fréchet differentiable. -/
theorem quadratic_affine_functional_contDiff_two
    (L : H →L[ℝ] H) (u : H) :
    ContDiff ℝ 2 (quadratic_affine_functional L u) := by
  -- Build smoothness directly from the explicit formula as a difference of smooth inner products.
  have h_quad : ContDiff ℝ 2 (fun y : H ↦ ⟪L y, y⟫_ℝ) := by
    simpa using (L.contDiff.inner ℝ (contDiff_id : ContDiff ℝ 2 (fun y : H ↦ y)))
  have h_lin : ContDiff ℝ 2 (fun y : H ↦ ⟪y, u⟫_ℝ) := by
    simpa using ((contDiff_id : ContDiff ℝ 2 (fun y : H ↦ y)).inner ℝ contDiff_const)
  simpa [quadratic_affine_functional] using h_quad.sub h_lin

section

variable [CompleteSpace H]

/-- Helper for Example 2.57: the quadratic part `y ↦ ⟪L y, y⟫` has derivative represented by
`(L + L†) x`. -/
private lemma quadratic_form_hasFDerivAt
    (L : H →L[ℝ] H) (x : H) :
    HasFDerivAt (fun y : H ↦ ⟪L y, y⟫_ℝ)
      (InnerProductSpace.toDual ℝ H ((L + L.adjoint) x)) x := by
  -- Differentiate the two inner-product entries and then rewrite the mixed term using the adjoint.
  have h_quad : HasFDerivAt (fun y : H ↦ ⟪L y, y⟫_ℝ)
      ((fderivInnerCLM ℝ (L x, x)).comp (L.prod (ContinuousLinearMap.id ℝ H))) x := by
    simpa using (L.hasFDerivAt.inner ℝ (ContinuousLinearMap.id ℝ H).hasFDerivAt)
  convert h_quad using 1
  ext h
  simp [fderivInnerCLM_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, InnerProductSpace.toDual_apply_apply,
    ContinuousLinearMap.adjoint_inner_left]
  rw [real_inner_comm x (L h)]

/-- Helper for Example 2.57: the affine linear term `y ↦ ⟪y, u⟫` has derivative represented by
`u`. -/
private lemma inner_right_hasFDerivAt
    (u x : H) :
    HasFDerivAt (fun y : H ↦ ⟪y, u⟫_ℝ)
      (InnerProductSpace.toDual ℝ H u) x := by
  -- Only the first inner-product entry varies, so the derivative is the corresponding linear form.
  have h_lin : HasFDerivAt (fun y : H ↦ ⟪y, u⟫_ℝ)
      ((fderivInnerCLM ℝ (x, u)).comp ((ContinuousLinearMap.id ℝ H).prod 0)) x := by
    simpa using ((ContinuousLinearMap.id ℝ H).hasFDerivAt.inner ℝ (hasFDerivAt_const u x))
  convert h_lin using 1
  ext h
  simp [fderivInnerCLM_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, InnerProductSpace.toDual_apply_apply]
  rw [real_inner_comm u h]

-- Proof sketch: expand `quadratic_affine_functional`, use bilinearity of the inner product, and
-- identify the linear part with the Riesz representative `(L + L.adjoint) x - u`.
/-- Example 2.57: the Fréchet derivative of `y ↦ ⟪L y, y⟫_ℝ - ⟪y, u⟫_ℝ` at `x` is the linear form
represented by `(L + L.adjoint) x - u`. -/
theorem quadratic_affine_functional_hasFDerivAt
    (L : H →L[ℝ] H) (u x : H) :
    HasFDerivAt (quadratic_affine_functional L u)
      (InnerProductSpace.toDual ℝ H (((L + L.adjoint) x) - u)) x := by
  -- Differentiate the quadratic and linear pieces separately, then identify the resulting linear form.
  have h_quad := quadratic_form_hasFDerivAt L x
  have h_lin := inner_right_hasFDerivAt u x
  convert h_quad.sub h_lin using 1
  ext h
  simp [sub_eq_add_neg, add_comm, add_left_comm]

/-- Example 2.57: the quadratic-affine functional `y ↦ ⟪L y, y⟫_ℝ - ⟪y, u⟫_ℝ` has gradient
`(L + L.adjoint) x - u` at every point `x`. -/
theorem quadratic_affine_functional_hasGradientAt
    (L : H →L[ℝ] H) (u x : H) :
    HasGradientAt (quadratic_affine_functional L u)
      ((L + L.adjoint) x - u) x := by
  simpa using (quadratic_affine_functional_hasFDerivAt L u x).hasGradientAt

-- Proof sketch: apply `gradient_eq` to the pointwise gradient formula.
/-- The gradient of `quadratic_affine_functional L u` is the affine map
`x ↦ (L + L.adjoint) x - u`. -/
theorem gradient_quadratic_affine_functional
    (L : H →L[ℝ] H) (u : H) :
    ∇ (quadratic_affine_functional L u) = fun x ↦ (L + L.adjoint) x - u := by
  exact gradient_eq (quadratic_affine_functional_hasGradientAt L u)

-- Proof sketch: the gradient map is affine with constant linear part
-- `L + L.adjoint`, so its Fréchet derivative is that operator at every point.
/-- The gradient map of `quadratic_affine_functional L u` has constant Fréchet derivative
`L + L.adjoint`. -/
theorem gradient_quadratic_affine_functional_hasFDerivAt
    (L : H →L[ℝ] H) (u x : H) :
    HasFDerivAt (∇ (quadratic_affine_functional L u))
      (L + L.adjoint) x := by
  -- Rewrite the gradient as an affine map and differentiate that explicit formula.
  rw [gradient_quadratic_affine_functional L u]
  simpa using ((L + L.adjoint).hasFDerivAt.sub_const u)

-- Proof sketch: take `fderiv` in the preceding `HasFDerivAt` statement.
/-- The Fréchet derivative of the gradient of `quadratic_affine_functional L u` is
`L + L.adjoint`. -/
theorem fderiv_gradient_quadratic_affine_functional
    (L : H →L[ℝ] H) (u x : H) :
    fderiv ℝ (∇ (quadratic_affine_functional L u)) x =
      (L + L.adjoint) := by
  -- The derivative is the linear part identified in the previous theorem.
  simpa using (gradient_quadratic_affine_functional_hasFDerivAt L u x).fderiv

end

/-! Source item: Chap02/Example_2_59 -/

noncomputable section


variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

private lemma half_symmetric_derivative
    (B : H →L[ℝ] H →L[ℝ] ℝ) (hB : B.toBilinForm.IsSymm) (x : H) :
    (1 / 2 : ℝ) •
        (((B.precompR H) x) (ContinuousLinearMap.id ℝ H) +
          ((B.precompL H) (ContinuousLinearMap.id ℝ H)) x) =
      B x := by
  ext y
  simp [Pi.smul_apply]
  rw [show (B y) x = (B x) y by simpa using hB.eq y x]
  ring_nf

/-- Example 2.59: for a symmetric continuous bilinear form `B`, the functional
`y ↦ (1 / 2) B(y, y) - ℓ(y)` is Fréchet differentiable at `x` with derivative `B(x, ·) - ℓ`. -/
theorem hasFDerivAt_half_bilinear_self_sub_linear
    (B : H →L[ℝ] H →L[ℝ] ℝ) (hB : B.toBilinForm.IsSymm)
    (ℓ : H →L[ℝ] ℝ) (x : H) :
    HasFDerivAt
      (fun y : H ↦ (1 / 2 : ℝ) * B y y - ℓ y)
      (B x - ℓ) x := by
  have hQuad : HasFDerivAt (fun y : H ↦ B y y)
      ((((B.precompR H) x) (ContinuousLinearMap.id ℝ H) +
          ((B.precompL H) (ContinuousLinearMap.id ℝ H)) x)) x := by
    simpa using
      (B.hasFDerivAt_of_bilinear
        (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.id ℝ H))
        (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.id ℝ H)))
  have hHalfScaled : HasFDerivAt
      (fun y : H ↦ (1 / 2 : ℝ) * B y y)
      ((1 / 2 : ℝ) •
        ((((B.precompR H) x) (ContinuousLinearMap.id ℝ H) +
          ((B.precompL H) (ContinuousLinearMap.id ℝ H)) x))) x := by
    simpa [Pi.smul_apply] using hQuad.const_smul (1 / 2 : ℝ)
  have hHalf : HasFDerivAt (fun y : H ↦ (1 / 2 : ℝ) * B y y) (B x) x := by
    convert hHalfScaled using 1
    exact (half_symmetric_derivative B hB x).symm
  simpa [sub_eq_add_neg] using hHalf.sub ℓ.hasFDerivAt

/-- The Fréchet derivative of the quadratic perturbation associated to a symmetric continuous
bilinear form is `B(x, ·) - ℓ`. -/
theorem fderiv_half_bilinear_self_sub_linear
    (B : H →L[ℝ] H →L[ℝ] ℝ) (hB : B.toBilinForm.IsSymm)
    (ℓ : H →L[ℝ] ℝ) (x : H) :
    fderiv ℝ (fun y : H ↦ (1 / 2 : ℝ) * B y y - ℓ y) x =
      B x - ℓ := by
  simpa using (hasFDerivAt_half_bilinear_self_sub_linear B hB ℓ x).fderiv

end

/-! Source item: Chap02/Example_2_60 -/


variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The least-squares residual associated to a bounded operator `L` and target vector `r`. -/
def leastSquaresResidual (L : H →L[ℝ] K) (r : K) : H → ℝ :=
  fun y ↦ ‖L y - r‖ ^ 2

/-- Evaluating the least-squares residual gives the squared norm of `L y - r`. -/
-- Proof sketch: unfold `leastSquaresResidual`; the statement is the defining equation.
@[simp] theorem leastSquaresResidual_apply (L : H →L[ℝ] K) (r : K) (y : H) :
    leastSquaresResidual L r y = ‖L y - r‖ ^ 2 := by
  -- This is exactly the defining formula of `leastSquaresResidual`.
  rfl

/-- Example 2.60: the least-squares residual `y ↦ ‖L y - r‖^2` is twice Fréchet differentiable on
`H`. The next two companion statements record its gradient and Hessian formulas in mathlib's
Fréchet-derivative language. -/
-- Proof sketch: write `leastSquaresResidual L r` as the squared norm of the affine map
-- `y ↦ L y - r`; smoothness follows from the smoothness of continuous linear maps, subtraction by a
-- constant, and `ContDiff.norm_sq`.
theorem leastSquaresResidual_contDiff (L : H →L[ℝ] K) (r : K) :
    ContDiff ℝ 2 (leastSquaresResidual L r) := by
  -- The residual map is affine, hence `C^2`, and `‖·‖^2` preserves that regularity.
  have hResidual : ContDiff ℝ 2 (fun y : H ↦ L y - r) := by
    simpa using L.contDiff.sub contDiff_const
  simpa [leastSquaresResidual] using (contDiff_norm_sq ℝ).comp hResidual

private theorem hasFDerivAt_residualMap (L : H →L[ℝ] K) (r : K) (x : H) :
    HasFDerivAt (fun y : H ↦ L y - r) L x := by
  simpa using L.hasFDerivAt.sub_const r

variable [CompleteSpace H] [CompleteSpace K]

/-- Example 2.60: the least-squares residual has gradient `2 L† (L x - r)` at every point `x`. -/
-- Proof sketch: differentiate the affine residual map `y ↦ L y - r`, compose with the standard
-- derivative formula for `y ↦ ‖y‖^2`, and rewrite the resulting functional using the adjoint of
-- `L`.
theorem leastSquaresResidual_hasGradientAt (L : H →L[ℝ] K) (r : K) (x : H) :
    HasGradientAt (leastSquaresResidual L r) ((2 : ℝ) • (L.adjoint (L x - r))) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hResidual := hasFDerivAt_residualMap L r x
  convert hResidual.norm_sq using 1
  ext y
  simp [InnerProductSpace.toDual_apply_apply, map_sub, two_smul, L.adjoint_inner_left]

/-- The Fréchet derivative of the least-squares residual is the continuous linear functional
represented by the gradient vector `2 (L† (L x - r))`. -/
theorem leastSquaresResidual_hasFDerivAt (L : H →L[ℝ] K) (r : K) (x : H) :
    HasFDerivAt (leastSquaresResidual L r)
      (InnerProductSpace.toDual ℝ H ((2 : ℝ) • (L.adjoint (L x - r)))) x := by
  simpa [hasGradientAt_iff_hasFDerivAt] using leastSquaresResidual_hasGradientAt L r x

/-- The gradient of the least-squares residual is the affine map
`x ↦ 2 • L† (L x - r)`. -/
theorem gradient_leastSquaresResidual (L : H →L[ℝ] K) (r : K) :
    ∇ (leastSquaresResidual L r) = fun x ↦ (2 : ℝ) • (L.adjoint (L x - r)) := by
  exact gradient_eq (leastSquaresResidual_hasGradientAt L r)

/-- The derivative of the gradient map of the least-squares residual is the constant Hessian
operator `2 L†L`. -/
-- Proof sketch: rewrite the gradient using its explicit affine formula and differentiate its linear
-- part.
theorem leastSquaresResidual_gradient_hasFDerivAt (L : H →L[ℝ] K) (r : K) (x : H) :
    HasFDerivAt (∇ (leastSquaresResidual L r))
      ((2 : ℝ) • (L.adjoint.comp L)) x := by
  rw [gradient_leastSquaresResidual L r]
  have hResidual := hasFDerivAt_residualMap L r x
  have hAffine :
      HasFDerivAt (fun y : H ↦ L.adjoint (L y - r)) (L.adjoint.comp L) x := by
    simpa [Function.comp_def] using L.adjoint.hasFDerivAt.comp x hResidual
  simpa using hAffine.const_smul (2 : ℝ)

/-- The Fréchet derivative of the least-squares gradient map is the constant Hessian operator
`2 L†L`. -/
theorem fderiv_gradient_leastSquaresResidual (L : H →L[ℝ] K) (r : K) (x : H) :
    fderiv ℝ (∇ (leastSquaresResidual L r)) x = (2 : ℝ) • (L.adjoint.comp L) := by
  simpa using (leastSquaresResidual_gradient_hasFDerivAt L r x).fderiv

/-! Source item: Chap02/Lemma_2_61 -/

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]

-- Proof sketch: a Fréchet derivative gives the usual little-o control of
-- `T (x + h) - T x - A h` as `h → 0` within `C`. Because `C` is a neighborhood of `x`, every
-- direction from `x` stays inside `C` along a short positive segment, so substituting `h = α • y`
-- and dividing by `α > 0` yields the one-sided directional limit defining the Gâteaux derivative
-- with the same operator `A`.
/-- Lemma 2.61 (1): if `C` is a neighborhood of `x` and `A` is the Fréchet derivative of `T` at
`x` within `C`, then for every direction `y` the one-sided directional difference quotient tends to
`A y`; equivalently, `T` is Gâteaux differentiable there and the two derivatives coincide. -/
theorem HasFDerivWithinAt.tendsto_directionalDifferenceQuotient
    {C : Set H} {T : H → K} {x : H} {A : H →L[ℝ] K}
    (hT : HasFDerivWithinAt T A C x) (hC : C ∈ 𝓝 x) :
    ∀ y : H,
      Filter.Tendsto (fun α : ℝ ↦ (1 / α) • (T (x + α • y) - T x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) := by
  simpa using
    (HasFDerivWithinAt.hasGateauxDerivativeWithinAt hT hC).tendsto_directionalDifferenceQuotient

-- Proof sketch: a Fréchet derivative within `C` implies continuity within `C` at `x` by the
-- standard calculus theorem. Since `C` is a neighborhood of `x`, continuity within `C` upgrades to
-- ordinary continuity at `x`.
/-- Lemma 2.61 (2): if `C` is a neighborhood of `x` and `T` is Fréchet differentiable at `x`
within `C`, then `T` is continuous at `x`. -/
theorem HasFDerivWithinAt.continuousAt_of_mem_nhds
    {C : Set H} {T : H → K} {x : H} {A : H →L[ℝ] K}
    (hT : HasFDerivWithinAt T A C x) (hC : C ∈ 𝓝 x) :
    ContinuousAt T x := by
  -- Fréchet differentiability gives continuity within `C`, and the neighborhood hypothesis
  -- upgrades that local continuity to ordinary continuity at `x`.
  simpa using hT.continuousWithinAt.continuousAt hC

/-! Source item: Chap02/Fact_2_62 -/


variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- Helper for Fact 2.62: a neighborhood of `x` contains every sufficiently short segment
`x + t • h` with `t ∈ [0, 1]`. -/
private lemma short_segment_subset_field_domain
    {U : Set H} {x : H} (hU : U ∈ 𝓝 x) :
    ∃ r > 0, ∀ ⦃h : H⦄ ⦃t : ℝ⦄, ‖h‖ < r → t ∈ Set.Icc (0 : ℝ) 1 → x + t • h ∈ U := by
  rcases Metric.mem_nhds_iff.1 hU with ⟨r, hrpos, hr⟩
  refine ⟨r, hrpos, ?_⟩
  intro h t hh ht
  apply hr
  have ht_nonneg : 0 ≤ t := ht.1
  have ht_le_one : t ≤ 1 := ht.2
  have hnorm : ‖t • h‖ < r := by
    calc
      ‖t • h‖ = ‖t‖ * ‖h‖ := norm_smul t h
      _ = t * ‖h‖ := by rw [Real.norm_of_nonneg ht_nonneg]
      _ ≤ 1 * ‖h‖ := by gcongr
      _ = ‖h‖ := by ring
      _ < r := hh
  simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_assoc] using hnorm

/-- Helper for Fact 2.62: the line derivative hypothesis gives the derivative of the segment curve
`s ↦ T (x + s • h)` at an arbitrary parameter `t`. -/
private lemma segment_curve_hasDerivAt
    {T : H → K} {DT : H → H →L[ℝ] K} {U : Set H} {x h : H} {t : ℝ}
    (hGateaux : ∀ y ∈ U, ∀ v : H, HasLineDerivAt ℝ T (DT y v) y v)
    (ht : x + t • h ∈ U) :
    HasDerivAt (fun s : ℝ ↦ T (x + s • h)) (DT (x + t • h) h) t := by
  -- Recenter the line-derivative statement at `x + t • h` and convert the time shift back to `t`.
  let path : ℝ → K := fun s ↦ T ((x + t • h) + s • h)
  have hLine : HasDerivAt path (DT (x + t • h) h) 0 := by
    simpa [HasLineDerivAt, path] using hGateaux (x + t • h) ht h
  have hLineShift : HasDerivAt path (DT (x + t • h) h) (-t + t) := by
    simpa using hLine
  simpa [path, add_assoc, add_left_comm, add_comm, add_smul, smul_add, mul_comm, mul_left_comm,
    mul_assoc, one_smul] using HasDerivAt.comp_const_add (-t) t hLineShift

/-- Helper for Fact 2.62: the segment remainder has derivative
`((DT (x + t • h) - DT x) h)` within `[0, 1]`. -/
private lemma segment_remainder_hasDerivWithinAt
    {T : H → K} {DT : H → H →L[ℝ] K} {U : Set H} {x h : H} {t : ℝ}
    (hGateaux : ∀ y ∈ U, ∀ v : H, HasLineDerivAt ℝ T (DT y v) y v)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hxt : x + t • h ∈ U) :
    HasDerivWithinAt
      (fun s : ℝ ↦ T (x + s • h) - T x - s • DT x h)
      ((DT (x + t • h) - DT x) h) (Set.Icc (0 : ℝ) 1) t := by
  -- Differentiate the three terms separately, then simplify the resulting linear expression.
  have hcurve :
      HasDerivAt (fun s : ℝ ↦ T (x + s • h)) (DT (x + t • h) h) t :=
    segment_curve_hasDerivAt hGateaux hxt
  have hlinear : HasDerivAt (fun s : ℝ ↦ s • DT x h) (DT x h) t := by
    simpa using (hasDerivAt_id' t).smul_const (DT x h)
  simpa [sub_eq_add_neg, ContinuousLinearMap.sub_apply] using
    ((hcurve.sub_const (T x)).sub hlinear).hasDerivWithinAt

/-- Helper for Fact 2.62: continuity of the operator field at `x` gives a uniform bound on the
remainder derivative along every short segment issuing from `x`. -/
private lemma uniform_operator_bound_on_short_segments
    {DT : H → H →L[ℝ] K} {U : Set H} {x : H}
    (hU : U ∈ 𝓝 x) (hcont : ContinuousWithinAt DT U x) :
    ∀ ε > 0, ∃ δ > 0, ∀ ⦃h : H⦄ ⦃t : ℝ⦄,
      ‖h‖ < δ → t ∈ Set.Icc (0 : ℝ) 1 →
      ‖((DT (x + t • h) - DT x) h)‖ ≤ ε * ‖h‖ := by
  intro ε εpos
  rcases short_segment_subset_field_domain hU with ⟨r, hrpos, hr⟩
  have hcontAt : ContinuousAt DT x := hcont.continuousAt hU
  rcases Metric.continuousAt_iff.1 hcontAt ε εpos with ⟨η, hηpos, hη⟩
  refine ⟨min r η, lt_min hrpos hηpos, ?_⟩
  intro h t hh ht
  have hh_r : ‖h‖ < r := lt_of_lt_of_le hh (min_le_left _ _)
  have hdist : dist (x + t • h) x < η := by
    have hdist_le : dist (x + t • h) x ≤ ‖h‖ := by
      have ht_nonneg : 0 ≤ t := ht.1
      have ht_le_one : t ≤ 1 := ht.2
      calc
        dist (x + t • h) x = ‖t • h‖ := by
          simp [dist_eq_norm, sub_eq_add_neg, add_assoc]
        _ = ‖t‖ * ‖h‖ := norm_smul t h
        _ = t * ‖h‖ := by rw [Real.norm_of_nonneg ht_nonneg]
        _ ≤ 1 * ‖h‖ := by gcongr
        _ = ‖h‖ := by ring
    exact lt_of_le_of_lt hdist_le (lt_of_lt_of_le hh (min_le_right _ _))
  have hnorm_op : ‖DT (x + t • h) - DT x‖ < ε := by
    simpa [dist_eq_norm] using hη hdist
  calc
    ‖((DT (x + t • h) - DT x) h)‖ ≤ ‖DT (x + t • h) - DT x‖ * ‖h‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ε * ‖h‖ := by gcongr

/-- Fact 2.62: if a derivative field `DT` gives the Gâteaux derivative of `T` at every point of a
neighborhood `U` of `x`, and `DT` is continuous at `x` along `U` for the operator norm, then `T`
has Fréchet derivative `DT x` at `x`. -/
-- Proof sketch: restrict `T` to short line segments `t ↦ x + t • v`, identify the derivative of
-- this curve with `DT (x + t • v) v`, and integrate along `[0, 1]`; continuity of `DT` at `x`
-- then makes the remainder term `o (‖v‖)`.
theorem hasFDerivAt_of_gateauxDerivative_continuousWithinAt
    {T : H → K} {DT : H → H →L[ℝ] K} {U : Set H} {x : H}
    (hU : U ∈ 𝓝 x)
    (hGateaux : HasGateauxDerivativeOn T DT U)
    (hcont : ContinuousWithinAt DT U x) :
    HasFDerivAt T (DT x) x := by
  -- We prove the small-o remainder estimate by controlling `T` along short line segments.
  have hLine : ∀ y ∈ U, ∀ v : H, HasLineDerivAt ℝ T (DT y v) y v := by
    intro y hy v
    exact HasGateauxDerivativeWithinAt.hasLineDerivAt (hGateaux y hy) v
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε εpos
  rcases short_segment_subset_field_domain hU with ⟨r, hrpos, hr⟩
  rcases uniform_operator_bound_on_short_segments hU hcont ε εpos with ⟨δ, hδpos, hδ⟩
  refine Metric.eventually_nhds_iff.2 ⟨min r δ, lt_min hrpos hδpos, ?_⟩
  intro h hh
  have hhnorm : ‖h‖ < min r δ := by
    simpa [dist_eq_norm] using hh
  have hh_r : ‖h‖ < r := lt_of_lt_of_le hhnorm (min_le_left _ _)
  have hh_δ : ‖h‖ < δ := lt_of_lt_of_le hhnorm (min_le_right _ _)
  have hseg :
      ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → x + t • h ∈ U := by
    intro t ht
    exact hr hh_r ht
  have hderiv :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt
          (fun s : ℝ ↦ T (x + s • h) - T x - s • DT x h)
          ((DT (x + t • h) - DT x) h) (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    exact segment_remainder_hasDerivWithinAt hLine ht (hseg ht)
  have hbound :
      ∀ t ∈ Set.Ico (0 : ℝ) 1,
        ‖((DT (x + t • h) - DT x) h)‖ ≤ ε * ‖h‖ := by
    intro t ht
    exact hδ hh_δ (Set.Ico_subset_Icc_self ht)
  -- The one-dimensional mean-value estimate turns the derivative bound
  -- into the desired remainder bound.
  have hmv :
      ‖(T (x + (1 : ℝ) • h) - T x - (1 : ℝ) • DT x h) -
          (T (x + (0 : ℝ) • h) - T x - (0 : ℝ) • DT x h)‖ ≤ ε * ‖h‖ := by
    simpa using norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
  simpa using hmv

/-! Source item: Chap02/Proposition_2_58 -/


variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Proposition 2.58: a continuous linear Gâteaux derivative field on the whole space
is the Fréchet derivative field. -/
private lemma hasFDerivAt_of_isGateauxDerivativeOn_univ
    (f : H → ℝ) (L : H →L[ℝ] H)
    (hGateaux : HasGateauxDerivativeOn f (fun x ↦ toDual ℝ H (L x)) Set.univ) (x : H) :
    HasFDerivAt f (toDual ℝ H (L x)) x := by
  let DT : H → H →L[ℝ] ℝ := fun y ↦ toDual ℝ H (L y)
  have hU : Set.univ ∈ 𝓝 x := by
    simp
  have hcont : ContinuousWithinAt DT Set.univ x := by
    exact ((toDual ℝ H).continuous.comp L.continuous).continuousWithinAt
  simpa [DT] using hasFDerivAt_of_gateauxDerivative_continuousWithinAt hU hGateaux hcont

/-- Helper for Proposition 2.58: a continuous linear Gâteaux gradient field is the Fréchet
gradient field. -/
private lemma hasGradientAt_of_isGateauxDerivativeOn_univ
    (f : H → ℝ) (L : H →L[ℝ] H)
    (hGateaux : HasGateauxDerivativeOn f (fun x ↦ toDual ℝ H (L x)) Set.univ) (x : H) :
    HasGradientAt f (L x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa using hasFDerivAt_of_isGateauxDerivativeOn_univ f L hGateaux x

/-- Helper for Proposition 2.58: restricting `f` to the line `t ↦ t • x` has derivative
`t * ⟪L x, x⟫_ℝ` when `∇f = L`. -/
-- This is the one-dimensional bridge from the Hilbert-space gradient hypothesis to the
-- fundamental theorem of calculus on the segment from `0` to `x`.
private lemma line_restriction_hasDerivAt
    (f : H → ℝ) (L : H →L[ℝ] H) (hgrad : ∀ x, HasGradientAt f (L x) x) (x : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ f (s • x)) (t * ⟪L x, x⟫_ℝ) t := by
  -- Compose the gradient derivative of `f` at `t • x` with the scalar line map `s ↦ s • x`.
  have hline : HasDerivAt (fun s : ℝ ↦ s • x) x t := by
    simpa using ((hasDerivAt_id t).smul_const x)
  have hcomp := (hgrad (t • x)).hasFDerivAt.comp_hasDerivAt (x := t) hline
  -- Simplify the resulting scalar derivative using linearity of `L` and the inner product.
  simpa [map_smul, inner_smul_left, mul_comm, mul_left_comm, mul_assoc]
    using hcomp

/-- Helper for Proposition 2.58: integrating the line restriction yields the quadratic increment
formula for `f`. -/
-- Once the derivative along `t ↦ t • x` is known explicitly, the scalar FTC on `[0,1]` gives
-- the value of `f x - f 0`.
private lemma quadratic_increment_formula
    (f : H → ℝ) (L : H →L[ℝ] H) (hgrad : ∀ x, HasGradientAt f (L x) x) (x : H) :
    f x - f 0 = (1 / 2 : ℝ) * ⟪L x, x⟫_ℝ := by
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ ↦ f (s • x)) (t * ⟪L x, x⟫_ℝ) t := by
    intro t ht
    exact line_restriction_hasDerivAt f L hgrad x t
  have hint :
      IntervalIntegrable (fun t : ℝ ↦ t * ⟪L x, x⟫_ℝ) MeasureTheory.volume 0 1 := by
    exact
      Continuous.intervalIntegrable (μ := MeasureTheory.volume)
        (show Continuous (fun t : ℝ ↦ t * ⟪L x, x⟫_ℝ) by fun_prop) 0 1
  -- Apply the scalar FTC to the line restriction `t ↦ f (t • x)`.
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hEval : ∫ t in (0 : ℝ)..1, t * ⟪L x, x⟫_ℝ = (1 / 2 : ℝ) * ⟪L x, x⟫_ℝ := by
    -- The remaining integral is the elementary integral of `t` times a constant.
    rw [intervalIntegral.integral_mul_const, integral_id]
    norm_num
  rw [show (1 : ℝ) • x = x by simp, show (0 : ℝ) • x = 0 by simp, hEval] at hFTC
  linarith

/-- Helper for Proposition 2.58: Example 2.57 gives the gradient of the quadratic model
`y ↦ c + (1 / 2) * ⟪L y, y⟫_ℝ`. -/
private lemma quadratic_model_hasGradientAt (L : H →L[ℝ] H) (c : ℝ) (x : H) :
    HasGradientAt (fun y : H ↦ c + (1 / 2 : ℝ) * ⟪L y, y⟫_ℝ)
      ((1 / 2 : ℝ) • ((L + L.adjoint) x)) x := by
  have hq :
      HasGradientAt (quadratic_affine_functional L 0) ((L + L.adjoint) x) x := by
    simpa [quadratic_affine_functional] using quadratic_affine_functional_hasGradientAt L 0 x
  have hscaled := hq.hasFDerivAt.const_smul (1 / 2 : ℝ)
  have hshifted := hscaled.const_add c
  convert hshifted.hasGradientAt using 1
  · ext y
    simp [quadratic_affine_functional]
  · apply (toDual ℝ H).injective
    ext y
    simp

/-- Helper for Proposition 2.58: Example 2.57 gives the `C²` regularity of the quadratic model
`y ↦ c + (1 / 2) * ⟪L y, y⟫_ℝ`. -/
private lemma quadratic_model_contDiff_two (L : H →L[ℝ] H) (c : ℝ) :
    ContDiff ℝ 2 (fun y : H ↦ c + (1 / 2 : ℝ) * ⟪L y, y⟫_ℝ) := by
  have hmodel :
      ContDiff ℝ 2 (fun y : H ↦ (1 / 2 : ℝ) * quadratic_affine_functional L 0 y) :=
    (quadratic_affine_functional_contDiff_two L 0).const_smul (1 / 2 : ℝ)
  simpa [quadratic_affine_functional] using contDiff_const.add hmodel

/-- Proposition 2.58: if the Gâteaux derivative field of `f` is the continuous linear map `L`,
then `f` is the quadratic function `x ↦ f 0 + (1 / 2) * ⟪L x, x⟫_ℝ`. -/
-- Proof sketch: first upgrade the Gâteaux field to the Fréchet gradient field using
-- `Fact_2_62`, then integrate the line restriction from `0` to `x`.
theorem gradient_eq_continuousLinearMap_eq_quadratic_form (f : H → ℝ) (L : H →L[ℝ] H)
    (hGateaux : HasGateauxDerivativeOn f (fun x ↦ toDual ℝ H (L x)) Set.univ) :
    f = fun x ↦ f 0 + (1 / 2 : ℝ) * ⟪L x, x⟫_ℝ := by
  let hgrad : ∀ x, HasGradientAt f (L x) x := fun x ↦
    hasGradientAt_of_isGateauxDerivativeOn_univ f L hGateaux x
  funext x
  -- The line-integral identity gives the increment of `f` from `0` to `x`.
  have hx := quadratic_increment_formula f L hgrad x
  linarith

/-- Proposition 2.58: a continuous linear map that is the Gâteaux gradient field of a real-valued
function is self-adjoint. -/
-- Proof sketch: upgrade to the Fréchet gradient field, rewrite `f` by the quadratic formula, and
-- compare with the canonical quadratic-gradient formula from Example 2.57.
theorem gradient_eq_continuousLinearMap_self_adjoint (f : H → ℝ) (L : H →L[ℝ] H)
    (hGateaux : HasGateauxDerivativeOn f (fun x ↦ toDual ℝ H (L x)) Set.univ) :
    IsSelfAdjoint L := by
  let hgrad : ∀ x, HasGradientAt f (L x) x := fun x ↦
    hasGradientAt_of_isGateauxDerivativeOn_univ f L hGateaux x
  have hquad := gradient_eq_continuousLinearMap_eq_quadratic_form f L hGateaux
  rw [isSelfAdjoint_iff']
  ext x
  -- Compare the given gradient of `f` with the gradient of the quadratic model at the same point.
  have hfx : HasGradientAt f (L x) x := hgrad x
  have hqx :
      HasGradientAt (fun y : H ↦ f 0 + (1 / 2 : ℝ) * ⟪L y, y⟫_ℝ)
        ((1 / 2 : ℝ) • ((L + L.adjoint) x)) x :=
    quadratic_model_hasGradientAt L (f 0) x
  have hrew : HasGradientAt f ((1 / 2 : ℝ) • ((L + L.adjoint) x)) x := by
    rw [hquad]
    simpa using hqx
  have hx : L x = (1 / 2 : ℝ) • ((L + L.adjoint) x) := hfx.unique hrew
  -- Clear the factor `1 / 2` to isolate the pointwise equality `L x = L.adjoint x`.
  have hsum : L x + L x = L x + L.adjoint x := by
    calc
      L x + L x = (2 : ℝ) • L x := by simp [two_smul]
      _ = (2 : ℝ) • ((1 / 2 : ℝ) • ((L + L.adjoint) x)) := by rw [hx]
      _ = (L + L.adjoint) x := by simp [smul_smul]
      _ = L x + L.adjoint x := by simp [add_apply]
  simpa [star_eq_adjoint] using (add_left_cancel hsum).symm

/-- Proposition 2.58: a real-valued function whose Gâteaux gradient field is a continuous linear
map is twice Fréchet differentiable on the whole space, in the sense of Definition 2.56. -/
theorem gradient_eq_continuousLinearMap_twiceFrechetDifferentiableWithinAt
    (f : H → ℝ) (L : H →L[ℝ] H)
    (hGateaux : HasGateauxDerivativeOn f (fun x ↦ toDual ℝ H (L x)) Set.univ) (x : H) :
    TwiceFrechetDifferentiableWithinAt ℝ f Set.univ x := by
  rw [gradient_eq_continuousLinearMap_eq_quadratic_form f L hGateaux]
  exact ContDiff.twiceFrechetDifferentiableWithinAt_univ (quadratic_model_contDiff_two L (f 0)) x

/-- Canonical strengthening of Proposition 2.58: a real-valued function whose Gâteaux gradient
field is a continuous linear map is `C²`. -/
theorem gradient_eq_continuousLinearMap_contDiff_two (f : H → ℝ) (L : H →L[ℝ] H)
    (hGateaux : HasGateauxDerivativeOn f (fun x ↦ toDual ℝ H (L x)) Set.univ) :
    ContDiff ℝ 2 f := by
  -- Rewrite `f` as the explicit quadratic model and then use the established `C²` regularity.
  rw [gradient_eq_continuousLinearMap_eq_quadratic_form f L hGateaux]
  exact quadratic_model_contDiff_two L (f 0)

/-! Source item: Chap02/Fact_2_63 -/

variable {H : Type u} {G : Type v} {K : Type w}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]

-- Proof sketch: compose the one-sided line derivatives from
-- `HasGateauxDerivativeWithinAt` with the Fréchet derivative of `R`; the additional Fréchet
-- conclusion is the standard composition theorem `HasFDerivAt.comp`.
/-- If `R` has Fréchet derivative `B` at `T x` and `T` has Gâteaux derivative `A` within `U`
at `x`, then `R ∘ T` has Gâteaux derivative `B.comp A` within `U` at `x`. -/
theorem HasFDerivAt.comp_hasGateauxDerivativeWithinAt
    {U : Set H} {x : H} {T : H → G} {R : G → K}
    {A : H →L[ℝ] G} {B : G →L[ℝ] K}
    (hR : HasFDerivAt R B (T x))
    (hTg : HasGateauxDerivativeWithinAt T A U x) :
    HasGateauxDerivativeWithinAt (R ∘ T) (B.comp A) U x := by
  rcases hTg with ⟨hSegments, hdir⟩
  refine ⟨hSegments, ?_⟩
  intro y
  let path : ℝ → G := fun α ↦ T (x + α • y)
  have hpath : HasDerivWithinAt path (A y) (Set.Ioi 0) 0 := hdir y
  have hRpath : HasFDerivAt R B (path 0) := by
    simpa [path] using hR
  simpa [path, Function.comp, ContinuousLinearMap.comp_apply] using
    hRpath.comp_hasDerivWithinAt 0 hpath

/-- Fact 2.63: if `R` has Fréchet derivative `B` at `T x` and `T` has Gâteaux derivative `A`
within `U` at `x`, then `R ∘ T` has Gâteaux derivative `B.comp A` within `U` at `x`; moreover,
if `T` is Fréchet differentiable at `x` with derivative `A`, then `R ∘ T` is Fréchet
differentiable at `x` with derivative `B.comp A`. -/
theorem hasGateauxDerivativeWithinAt_and_hasFDerivAt_comp
    {U : Set H} {x : H} {T : H → G} {R : G → K}
    {A : H →L[ℝ] G} {B : G →L[ℝ] K}
    (hR : HasFDerivAt R B (T x))
    (hTg : HasGateauxDerivativeWithinAt T A U x) :
    HasGateauxDerivativeWithinAt (R ∘ T) (B.comp A) U x ∧
      (HasFDerivAt T A x → HasFDerivAt (R ∘ T) (B.comp A) x) := by
  refine ⟨HasFDerivAt.comp_hasGateauxDerivativeWithinAt hR hTg, ?_⟩
  intro hT
  simpa [Function.comp] using hR.comp x hT

/-! Source item: Chap02/Lemma_2_64 -/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

variable {U : Set H} {β : NNReal} {f : H → ℝ}
private lemma norm_sub_gradientWithin_le
    (hgrad : LipschitzOnWith β (gradientWithin f U) U) {x y : H}
    (hx : x ∈ U) (hy : y ∈ U) :
    ‖gradientWithin f U x - gradientWithin f U y‖ ≤ (β : ℝ) * ‖x - y‖ := by
  have h' := hgrad hx hy
  have h'' := (ENNReal.toReal_le_toReal (edist_ne_top _ _) (by finiteness)).2 h'
  simpa [edist_dist, dist_eq_norm] using h''

section

variable (hU_open : IsOpen U) (hU_convex : Convex ℝ U)
variable (hf : DifferentiableOn ℝ f U)
variable (hgrad : LipschitzOnWith β (gradientWithin f U) U)

omit [CompleteSpace H] in
private lemma lineMap_mem (hU_convex : Convex ℝ U) {x y : H} (hx : x ∈ U) (hy : y ∈ U) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap x y t ∈ U :=
  hU_convex.lineMap_mem hx hy ht

private lemma hasDerivAt_comp_lineMap_gradientWithin
    (hU_open : IsOpen U) (hf : DifferentiableOn ℝ f U) {x y : H} {t : ℝ}
    (hz : AffineMap.lineMap x y t ∈ U) :
    HasDerivAt (fun s : ℝ ↦ f (AffineMap.lineMap x y s))
      (⟪gradientWithin f U (AffineMap.lineMap x y t), y - x⟫_ℝ) t := by
  let z := AffineMap.lineMap x y t
  have hfd : HasFDerivAt f (fderiv ℝ f z) z := by
    exact (hf.differentiableAt (hU_open.mem_nhds hz)).hasFDerivAt
  have hcomp :
      HasDerivAt (fun s : ℝ ↦ f (AffineMap.lineMap x y s)) ((fderiv ℝ f z) (y - x)) t := by
    simpa [z] using hfd.comp_hasDerivAt t (AffineMap.hasDerivAt (AffineMap.lineMap x y))
  have hinner : (fderiv ℝ f z) (y - x) = ⟪gradientWithin f U z, y - x⟫_ℝ := by
    rw [← fderivWithin_of_isOpen hU_open hz]
    exact (hf z hz).hasGradientWithinAt.fderivWithin_apply (hU_open.uniqueDiffWithinAt hz)
  simpa [z, hinner] using hcomp

private lemma gradientWithin_lineMap_continuousOn
    (hU_convex : Convex ℝ U) (hgrad : LipschitzOnWith β (gradientWithin f U) U)
    {x y : H} (hx : x ∈ U) (hy : y ∈ U) :
    ContinuousOn (fun t : ℝ ↦ gradientWithin f U (AffineMap.lineMap x y t))
      (Set.Icc (0 : ℝ) 1) := by
  have hcont : ContinuousOn (gradientWithin f U) U := hgrad.continuousOn
  refine hcont.comp AffineMap.lineMap_continuous.continuousOn ?_
  intro t ht
  exact lineMap_mem hU_convex hx hy ht

private lemma remainder_integrand_norm_bound
    (hU_convex : Convex ℝ U) (hgrad : LipschitzOnWith β (gradientWithin f U) U)
    {x y : H} (hx : x ∈ U) (hy : y ∈ U) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |⟪gradientWithin f U (AffineMap.lineMap x y t) - gradientWithin f U x, y - x⟫_ℝ|
      ≤ (β : ℝ) * ‖y - x‖ ^ 2 * t := by
  have hz : AffineMap.lineMap x y t ∈ U := lineMap_mem hU_convex hx hy ht
  have hgrad_norm :
      ‖gradientWithin f U (AffineMap.lineMap x y t) - gradientWithin f U x‖
        ≤ (β : ℝ) * ‖AffineMap.lineMap x y t - x‖ :=
    norm_sub_gradientWithin_le hgrad hz hx
  have hline : ‖AffineMap.lineMap x y t - x‖ = t * ‖y - x‖ := by
    have hdist : dist x (AffineMap.lineMap x y t) = ‖t‖ * dist x y := dist_left_lineMap x y t
    have htnorm : ‖t‖ = t := abs_of_nonneg ht.1
    simpa [dist_eq_norm, norm_sub_rev, htnorm, mul_comm] using hdist
  calc
    |⟪gradientWithin f U (AffineMap.lineMap x y t) - gradientWithin f U x, y - x⟫_ℝ|
        ≤ ‖gradientWithin f U (AffineMap.lineMap x y t) - gradientWithin f U x‖ * ‖y - x‖ := by
          exact abs_real_inner_le_norm _ _
    _ ≤ ((β : ℝ) * ‖AffineMap.lineMap x y t - x‖) * ‖y - x‖ := by
      gcongr
    _ = ((β : ℝ) * (t * ‖y - x‖)) * ‖y - x‖ := by
      rw [hline]
    _ = (β : ℝ) * ‖y - x‖ ^ 2 * t := by
      ring

include hU_open hU_convex hf hgrad

/-- Lemma 2.64 (1): on an open convex set, a Fréchet differentiable function whose gradient
is `β`-Lipschitz has first-order Taylor remainder at most `(β / 2) * ‖y - x‖^2`. -/
theorem abs_sub_sub_inner_gradientWithin_le_half_mul
    {x y : H} (hx : x ∈ U) (hy : y ∈ U) :
    |f y - f x - ⟪y - x, gradientWithin f U x⟫_ℝ| ≤
      ((β : ℝ) / 2) * ‖y - x‖ ^ 2 := by
  let φ : ℝ → ℝ := fun t ↦ f (AffineMap.lineMap x y t)
  let ψ : ℝ → ℝ := fun t ↦ ⟪gradientWithin f U (AffineMap.lineMap x y t), y - x⟫_ℝ
  let ρ : ℝ → ℝ := fun t ↦
    ⟪gradientWithin f U (AffineMap.lineMap x y t) - gradientWithin f U x, y - x⟫_ℝ
  -- Differentiate `f` along the segment on the whole interval `[0,1]`.
  have hψ_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt φ (ψ t) t := by
    intro t ht
    have hz : AffineMap.lineMap x y t ∈ U := by
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le zero_le_one] using ht
      exact lineMap_mem hU_convex hx hy ht'
    simpa [φ, ψ] using hasDerivAt_comp_lineMap_gradientWithin hU_open hf hz
  -- Continuity of the gradient along the segment gives interval integrability.
  have hgradCont :
      ContinuousOn (fun t : ℝ ↦ gradientWithin f U (AffineMap.lineMap x y t)) (Set.Icc (0 : ℝ) 1) :=
    gradientWithin_lineMap_continuousOn hU_convex hgrad hx hy
  have hψ_cont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
    simpa [ψ] using hgradCont.inner continuousOn_const
  have hψ_int : IntervalIntegrable ψ MeasureTheory.volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one hψ_cont
  -- The fundamental theorem of calculus identifies the segment integral with `f y - f x`.
  have hFTC : ∫ t in 0..1, ψ t = f y - f x := by
    simpa [φ, ψ, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt hψ_deriv hψ_int
  have hρ_eq : (fun t : ℝ ↦ ψ t - ψ 0) = ρ := by
    funext t
    simp [ψ, ρ, AffineMap.lineMap_apply_zero, inner_sub_left]
  have hconst_int : IntervalIntegrable (fun _ : ℝ ↦ ψ 0) MeasureTheory.volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one continuousOn_const
  have hρ_int : IntervalIntegrable ρ MeasureTheory.volume 0 1 := by
    have hρ_cont : ContinuousOn ρ (Set.Icc (0 : ℝ) 1) := by
      simpa [ρ] using (hgradCont.sub continuousOn_const).inner continuousOn_const
    exact ContinuousOn.intervalIntegrable_of_Icc zero_le_one hρ_cont
  have hrem : f y - f x - ⟪gradientWithin f U x, y - x⟫_ℝ = ∫ t in 0..1, ρ t := by
    calc
      f y - f x - ⟪gradientWithin f U x, y - x⟫_ℝ = (∫ t in 0..1, ψ t) - ψ 0 := by
        rw [← hFTC]
        simp [ψ, AffineMap.lineMap_apply_zero]
      _ = (∫ t in 0..1, ψ t) - ∫ t in 0..1, ψ 0 := by
        simp [intervalIntegral.integral_const]
      _ = ∫ t in 0..1, (ψ t - ψ 0) := by
        rw [intervalIntegral.integral_sub hψ_int hconst_int]
      _ = ∫ t in 0..1, ρ t := by
        rw [hρ_eq]
  have hρ_abs_int : IntervalIntegrable (fun t : ℝ ↦ |ρ t|) MeasureTheory.volume 0 1 := hρ_int.abs
  have hbound_int :
      IntervalIntegrable (fun t : ℝ ↦ (β : ℝ) * ‖y - x‖ ^ 2 * t) MeasureTheory.volume 0 1 := by
    refine Continuous.intervalIntegrable ?_ 0 1
    continuity
  have hbound_mono :
      (∫ t in 0..1, |ρ t|) ≤ ∫ t in 0..1, (β : ℝ) * ‖y - x‖ ^ 2 * t := by
    refine intervalIntegral.integral_mono_on zero_le_one hρ_abs_int hbound_int ?_
    intro t ht
    simpa [ρ] using remainder_integrand_norm_bound hU_convex hgrad hx hy ht
  calc
    |f y - f x - ⟪y - x, gradientWithin f U x⟫_ℝ|
        = |f y - f x - ⟪gradientWithin f U x, y - x⟫_ℝ| := by
          rw [real_inner_comm]
    _ = |∫ t in 0..1, ρ t| := by
      rw [hrem]
    _ ≤ ∫ t in 0..1, |ρ t| := by
      exact intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ t in 0..1, (β : ℝ) * ‖y - x‖ ^ 2 * t := hbound_mono
    _ = ((β : ℝ) / 2) * ‖y - x‖ ^ 2 := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring

end

section

variable (hgrad : LipschitzOnWith β (gradientWithin f U) U)

include hgrad

/-- Lemma 2.64 (2): for points of `U`, the gradient increment paired with `x - y` is bounded in
absolute value by `β * ‖y - x‖^2`. -/
theorem abs_inner_sub_gradientWithin_sub_le_mul
    {x y : H} (hx : x ∈ U) (hy : y ∈ U) :
    |⟪x - y, gradientWithin f U x - gradientWithin f U y⟫_ℝ| ≤
      (β : ℝ) * ‖y - x‖ ^ 2 := by
  have hgrad_norm : ‖gradientWithin f U x - gradientWithin f U y‖ ≤ (β : ℝ) * ‖x - y‖ :=
    norm_sub_gradientWithin_le hgrad hx hy
  calc
    |⟪x - y, gradientWithin f U x - gradientWithin f U y⟫_ℝ|
        ≤ ‖x - y‖ * ‖gradientWithin f U x - gradientWithin f U y‖ := by
          exact abs_real_inner_le_norm _ _
    _ ≤ ‖x - y‖ * ((β : ℝ) * ‖x - y‖) := by
      gcongr
    _ = (β : ℝ) * ‖x - y‖ ^ 2 := by
      ring
    _ = (β : ℝ) * ‖y - x‖ ^ 2 := by
      rw [norm_sub_rev]

end

/-! Source item: Chap02/Example_2_65 -/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Example 2.65: on a real Hilbert space, the norm has Fréchet derivative at each nonzero point
`x`, represented by the continuous linear functional corresponding to `x / ‖x‖`. -/
theorem norm_hasFDerivAt {x : H} (hx : x ≠ 0) :
    HasFDerivAt (fun y : H ↦ ‖y‖) (toDual ℝ H (‖x‖⁻¹ • x)) x := by
  have hsq : HasFDerivAt (fun y : H ↦ ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    hasStrictFDerivAt_norm_sq x |>.hasFDerivAt
  have hcomp : HasFDerivAt (fun y : H ↦ Real.sqrt (‖y‖ ^ 2))
      ((1 / (2 * Real.sqrt (‖x‖ ^ 2))) • (2 • innerSL ℝ x)) x :=
    hsq.sqrt (by positivity)
  convert hcomp using 1
  · ext y
    rw [Real.sqrt_sq (norm_nonneg y)]
  · have hs : Real.sqrt (‖x‖ ^ 2) = ‖x‖ := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)]
    rw [hs]
    ext y
    simp
    ring

/-- Example 2.65 in gradient form: the norm has gradient `x / ‖x‖` at each nonzero point `x`. -/
theorem norm_hasGradientAt {x : H} (hx : x ≠ 0) :
    HasGradientAt (fun y : H ↦ ‖y‖) (‖x‖⁻¹ • x) x := by
  simpa using (norm_hasFDerivAt hx).hasGradientAt

/-- The gradient of the norm at a nonzero point is the normalized vector `x / ‖x‖`. -/
theorem gradient_norm {x : H} (hx : x ≠ 0) :
    ∇ (fun y : H ↦ ‖y‖) x = ‖x‖⁻¹ • x :=
  (norm_hasGradientAt hx).gradient

omit [CompleteSpace H] in
/-- The one-sided directional difference quotients of the norm at the origin converge to `‖y‖`. -/
theorem norm_zero_directional_difference_quotient_tendsto (y : H) :
    Filter.Tendsto
      (fun α : ℝ ↦ (‖(0 : H) + α • y‖ - ‖(0 : H)‖) / α)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ‖y‖) := by
  have hEq :
      (fun α : ℝ ↦ (‖(0 : H) + α • y‖ - ‖(0 : H)‖) / α) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        fun _ : ℝ ↦ ‖y‖ := by
    filter_upwards [self_mem_nhdsWithin] with α hα
    have hαpos : 0 < α := hα
    rw [norm_zero, zero_add, sub_zero, norm_smul, Real.norm_of_nonneg hαpos.le]
    field_simp [hαpos.ne']
  exact tendsto_const_nhds.congr' hEq.symm

omit [CompleteSpace H] in
/-- Example 2.65: the norm is not Gâteaux differentiable at the origin on a nontrivial real
Hilbert space. -/
theorem not_gateauxDifferentiableAt_norm_zero [Nontrivial H] :
    ¬ GateauxDifferentiableAt (fun y : H ↦ ‖y‖) (0 : H) := by
  intro h
  rcases h with ⟨A, hA⟩
  obtain ⟨y, hy⟩ := exists_ne (0 : H)
  have hnorm_y :
      Filter.Tendsto (fun α : ℝ ↦ (1 / α) * (‖(0 : H) + α • y‖ - ‖(0 : H)‖))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ‖y‖) := by
    simpa [one_div, div_eq_mul_inv, mul_comm] using
      norm_zero_directional_difference_quotient_tendsto y
  have hAy : A y = ‖y‖ :=
    tendsto_nhds_unique (hA.tendsto_directionalDifferenceQuotient y) hnorm_y
  have hnorm_neg :
      Filter.Tendsto (fun α : ℝ ↦ (1 / α) * (‖(0 : H) + α • (-y)‖ - ‖(0 : H)‖))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ‖y‖) := by
    simpa [norm_neg, one_div, div_eq_mul_inv, mul_comm] using
      norm_zero_directional_difference_quotient_tendsto (-y)
  have hAneg : A (-y) = ‖y‖ :=
    tendsto_nhds_unique (hA.tendsto_directionalDifferenceQuotient (-y)) hnorm_neg
  have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy
  have : -‖y‖ = ‖y‖ := by
    calc
      -‖y‖ = A (-y) := by rw [map_neg, hAy]
      _ = ‖y‖ := hAneg
  linarith

omit [CompleteSpace H] in
/-- No continuous linear functional can realize all one-sided directional derivatives of the norm at
the origin on a nontrivial real Hilbert space; equivalently, the norm is not Gâteaux
differentiable there. -/
theorem not_exists_gateauxDerivative_norm_zero [Nontrivial H] :
    ¬ ∃ A : H →L[ℝ] ℝ,
      ∀ y : H,
        Filter.Tendsto
          (fun α : ℝ ↦ (‖(0 : H) + α • y‖ - ‖(0 : H)‖) / α)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (A y)) := by
  intro h
  rcases h with ⟨A, hA⟩
  have hnot : ¬ GateauxDifferentiableAt (fun y : H ↦ ‖y‖) (0 : H) :=
    not_gateauxDifferentiableAt_norm_zero
  apply hnot
  refine ⟨A, ?_⟩
  rw [hasGateauxDerivativeAt_iff_tendsto_directionalDifferenceQuotient]
  intro y
  simpa [one_div, div_eq_mul_inv, mul_comm] using hA y

/-! Source item: Chap02/Fact_2_66 -/

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- Fact 2.66: textbook open-neighborhood form of symmetry of the second Fréchet derivative.
If `T` admits a Fréchet derivative field `DT` on an open neighborhood `U` of `x`, and `DT` is
Fréchet differentiable at `x` with derivative `D2T`, then the bilinear map `(y, z) ↦ D2T y z`
is symmetric. -/
-- Proof sketch: because `U` is an open neighborhood of `x`, the hypotheses give a first
-- derivative field for `T` on some neighborhood of `x`; then apply
-- `second_derivative_symmetric_of_eventually_of_real` to the derivative field `DT`.
theorem secondFrechetDerivAt_symmetric
    {T : H → K} {DT : H → H →L[ℝ] K} {D2T : H →L[ℝ] H →L[ℝ] K}
    {U : Set H} {x : H}
    (hU : IsOpen U) (hx : x ∈ U)
    (hT : ∀ y ∈ U, HasFDerivAt T (DT y) y)
    (hDT : HasFDerivAt DT D2T x) :
    ∀ y z : H, D2T y z = D2T z y := by
  -- Route correction: use the abstract symmetry theorem for second Fréchet derivatives
  -- after converting the open-neighborhood derivative field into an eventual one at `x`.
  have hT_eventually : ∀ᶠ y in nhds x, HasFDerivAt T (DT y) y := by
    -- The openness of `U` gives a neighborhood of `x` contained in `U`.
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hT y hy
  intro y z
  -- The mathlib Schwarz theorem now gives symmetry of the bilinear second derivative.
  exact second_derivative_symmetric_of_eventually_of_real hT_eventually hDT y z

/-! Source item: Chap02/Example_2_67 -/


variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Example 2.67: after transporting the gradient field through the Riesz map,
the symmetry of mixed second derivatives yields symmetry of the Hessian operator. -/
private theorem gradientWithin_fderiv_isSymmetric_aux
    {f : H → ℝ} {U : Set H} {x : H} {A : H →L[ℝ] H}
    (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ᶠ y in nhds x, DifferentiableWithinAt ℝ f U y)
    (hA : HasFDerivWithinAt (gradientWithin f U) A U x) :
    A.IsSymmetric := by
-- Proof sketch: apply `second_derivative_symmetric_of_eventually` to the derivative field
-- `toDualMap ℝ H ∘ gradientWithin f U`; the eventual differentiability hypothesis ensures that
-- this is the actual first derivative of `f` near `x`, and the resulting equality of mixed second
-- derivatives is exactly the symmetry of `A`.
  let f' : H → H →L[ℝ] ℝ := fun y ↦ (toDualMap ℝ H) (gradientWithin f U y)
  -- Near `x`, the transported gradient is the genuine Fréchet derivative of `f`.
  have hf' : ∀ᶠ y in nhds x, HasFDerivAt f (f' y) y := by
    filter_upwards [hU.mem_nhds hx, hf] with y hyU hyf
    have hy_grad : HasGradientWithinAt f (gradientWithin f U y) U y := hyf.hasGradientWithinAt
    have hy_deriv : HasFDerivAt f ((toDual ℝ H) (gradientWithin f U y)) y :=
      hy_grad.hasFDerivWithinAt.hasFDerivAt (hU.mem_nhds hyU)
    simpa [f', toDual_apply_eq_toDualMap_apply] using hy_deriv
  -- The derivative of the transported gradient field is the transported Hessian operator.
  have hA' : HasFDerivAt f' ((toDualMap ℝ H).toContinuousLinearMap.comp A) x := by
    have hA_at : HasFDerivAt (gradientWithin f U) A x := hA.hasFDerivAt (hU.mem_nhds hx)
    simpa [f'] using (toDualMap ℝ H).toContinuousLinearMap.hasFDerivAt.comp x hA_at
  -- Schwarz symmetry for the dual-valued first-derivative field translates back to `A`.
  intro u v
  have hs := second_derivative_symmetric_of_eventually hf' hA' u v
  simpa [f', toDualMap_apply_apply, real_inner_comm] using hs

/-- Example 2.67: if `U` is an open neighborhood of `x` in a real Hilbert space, `f` is
Fréchet differentiable on a neighborhood of `x` inside `U`, and the genuine gradient field
`gradientWithin f U` has Fréchet derivative `A` at `x` within `U`, then the Hessian operator `A`
is self-adjoint. -/
theorem gradientWithin_fderiv_isSelfAdjoint
    {f : H → ℝ} {U : Set H} {x : H} {A : H →L[ℝ] H}
    (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ᶠ y in nhds x, DifferentiableWithinAt ℝ f U y)
    (hA : HasFDerivWithinAt (gradientWithin f U) A U x) :
    IsSelfAdjoint A :=
  (gradientWithin_fderiv_isSymmetric_aux hU hx hf hA).isSelfAdjoint

/-- Textbook symmetry reformulation of `gradientWithin_fderiv_isSelfAdjoint`. -/
theorem gradientWithin_fderiv_isSymmetric
    {f : H → ℝ} {U : Set H} {x : H} {A : H →L[ℝ] H}
    (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ᶠ y in nhds x, DifferentiableWithinAt ℝ f U y)
    (hA : HasFDerivWithinAt (gradientWithin f U) A U x) :
    A.IsSymmetric :=
  (gradientWithin_fderiv_isSelfAdjoint hU hx hf hA).isSymmetric

/-- The Hessian identity corresponding to self-adjointness of the Fréchet derivative of the
gradient field. -/
-- Proof sketch: apply the canonical symmetry theorem
-- `gradientWithin_fderiv_isSelfAdjoint`.
theorem gradientWithin_fderiv_inner_symmetric
    {f : H → ℝ} {U : Set H} {x : H} {A : H →L[ℝ] H}
    (hU : IsOpen U) (hx : x ∈ U)
    (hf : ∀ᶠ y in nhds x, DifferentiableWithinAt ℝ f U y)
    (hA : HasFDerivWithinAt (gradientWithin f U) A U x) :
    ∀ u v : H, ⟪A u, v⟫_ℝ = ⟪u, A v⟫_ℝ := by
  simpa [LinearMap.IsSymmetric] using
    (gradientWithin_fderiv_isSelfAdjoint hU hx hf hA).isSymmetric

/-! Source item:
`TheoremLib/Attouch_Comparative_analysis_of_accelerated_gradient_algorithms_for_convex_optimization_high_and_super_resolution_ODE_approach_2024/items/ext_def_1` -/

/-- A gradient map is `L`-Lipschitz continuous. -/
def IsLipschitzGradient {H : Type*} [NormedAddCommGroup H]
    (L : ℝ) (grad : H → H) : Prop :=
  0 ≤ L ∧ ∀ x y : H, ‖grad x - grad y‖ ≤ L * ‖x - y‖

/-! Source item:
`TheoremLib/Attouch_Comparative_analysis_of_accelerated_gradient_algorithms_for_convex_optimization_high_and_super_resolution_ODE_approach_2024/items/ext_def_2` -/

/-- A convex smooth minimization problem together with a specified minimizer. -/
def IsConvexSmoothMinimization {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (grad : H → H) (L : ℝ) (xStar : H) : Prop :=
  ConvexOn ℝ Set.univ f ∧ (∀ x, HasGradientAt f (grad x) x) ∧
  IsLipschitzGradient L grad ∧ ∀ x, f xStar ≤ f x

/-- `f` is C3, with the supplied gradient, Hessian, and third derivative. -/
def IsC3Objective {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (grad : H → H) (hess : H → H → H)
    (third : H → H → H → H) : Prop :=
  ContDiff ℝ 3 f ∧
  (∀ x, HasGradientAt f (grad x) x) ∧
  (∀ x v, fderiv ℝ grad x v = hess x v) ∧
  (∀ x u v, fderiv ℝ (fun z => hess z u) x v = third x v u)

/-- The second-derivative chain rule for a C3 gradient along a C2 trajectory. -/
def HigherDerivativesAlong {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (grad : H → H) (hess : H → H → H) (third : H → H → H → H)
    (X vel acc d2GradAlong : ℝ → H) : Prop :=
  IsC3Objective f grad hess third ∧ ContDiff ℝ 2 X ∧
  (∀ t : ℝ, HasDerivAt X (vel t) t) ∧
  (∀ t : ℝ, HasDerivAt vel (acc t) t) ∧
  ∀ t : ℝ, d2GradAlong t =
    third (X t) (vel t) (vel t) + hess (X t) (acc t)
