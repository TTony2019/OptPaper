import Mathlib
import Foundation.Hilbert.WeakTopology

/-!
# Projection BestApproximation

Best approximations, proximinal and Chebyshev sets, metric projections, projection continuity, and affine/subspace projection formulas.
-/

open scoped InnerProductSpace
open Filter
open scoped InnerProductSpace Topology
open Filter Bornology
open scoped InnerProductSpace Pointwise
open scoped Pointwise InnerProductSpace
open EuclideanGeometry

/-! Source item: Chap03/Definition_3_8 -/
universe u

variable {X : Type u} [PseudoMetricSpace X]

/-- Definition 3.8: a point `p` is a best approximation to `x` from `C` when it lies in `C` and
realizes the distance from `x` to `C`. -/
abbrev IsBestApproximation (x : X) (C : Set X) (p : X) : Prop :=
  p ∈ C ∧ dist x p = Metric.infDist x C

/-- Definition 3.8: the set-valued projector onto `C` sends `x` to the set of best
approximations to `x` from `C`. -/
def setValuedProjector (C : Set X) : X → Set X :=
  fun x ↦ {p | IsBestApproximation x C p}

/-- Membership in the set-valued projector is exactly the best-approximation property. -/
@[simp] theorem mem_setValuedProjector_iff {C : Set X} {x p : X} :
    p ∈ setValuedProjector C x ↔ IsBestApproximation x C p :=
  Iff.rfl

/-- A best approximation is exactly a point of `C` whose distance to `x`
equals `Metric.infDist x C`. -/
@[simp] theorem isBestApproximation_iff_mem_and_dist_eq_infDist (x : X) (C : Set X) (p : X) :
    IsBestApproximation x C p ↔ p ∈ C ∧ dist x p = Metric.infDist x C :=
  Iff.rfl

/-- Definition 3.8: a set is proximinal when every point of the ambient space has at least one
best approximation in that set. -/
def IsProximinalIn (C : Set X) : Prop :=
  ∀ x : X, ∃ p : X, IsBestApproximation x C p

/-- Compatibility alias for the chapter's earlier `IsProximal` name. -/
abbrev IsProximal (C : Set X) : Prop :=
  IsProximinalIn C

/-- A set is proximinal exactly when each point admits a best approximation from the set. -/
@[simp] theorem isProximinalIn_iff_forall_exists_bestApproximation (C : Set X) :
    IsProximinalIn C ↔ ∀ x : X, ∃ p : X, IsBestApproximation x C p :=
  Iff.rfl

/-- A set is proximinal exactly when every value of its set-valued projector is nonempty. -/
@[simp] theorem isProximinalIn_iff_forall_setValuedProjector_nonempty (C : Set X) :
    IsProximinalIn C ↔ ∀ x : X, (setValuedProjector C x).Nonempty := by
  simp [IsProximinalIn, Set.Nonempty]

/-- Compatibility form of `isProximinalIn_iff_forall_exists_bestApproximation`. -/
@[simp] theorem isProximal_iff_forall_exists_bestApproximation (C : Set X) :
    IsProximal C ↔ ∀ x : X, ∃ p : X, IsBestApproximation x C p :=
  isProximinalIn_iff_forall_exists_bestApproximation C

/-- Compatibility form of `isProximinalIn_iff_forall_setValuedProjector_nonempty`. -/
@[simp] theorem isProximal_iff_forall_setValuedProjector_nonempty (C : Set X) :
    IsProximal C ↔ ∀ x : X, (setValuedProjector C x).Nonempty :=
  isProximinalIn_iff_forall_setValuedProjector_nonempty C

/-- A set is Chebyshev when every point of the ambient space has a unique best approximation in
that set. -/
def IsChebyshev (C : Set X) : Prop :=
  ∀ x : X, ∃! p : X, IsBestApproximation x C p

/-- A set is Chebyshev exactly when each point admits a unique best approximation from the set. -/
@[simp] theorem isChebyshev_iff_forall_existsUnique_bestApproximation (C : Set X) :
    IsChebyshev C ↔ ∀ x : X, ∃! p : X, IsBestApproximation x C p :=
  Iff.rfl

/-- A set is Chebyshev exactly when each value of its set-valued projector is a singleton. -/
@[simp] theorem isChebyshev_iff_forall_existsUnique_mem_setValuedProjector (C : Set X) :
    IsChebyshev C ↔ ∀ x : X, ∃! p : X, p ∈ setValuedProjector C x := by
  simp [IsChebyshev]

/-- For a Chebyshev set, the projection point of `x` onto `C` is the unique best approximation in
the ambient space. -/
noncomputable def projectionPoint (C : Set X) (hC : IsChebyshev C) (x : X) : X :=
  (hC x).choose

/-- For a Chebyshev set, the chosen projection point belongs to the set-valued projector. -/
@[simp] theorem projectionPoint_mem_setValuedProjector (C : Set X) (hC : IsChebyshev C) (x : X) :
    projectionPoint C hC x ∈ setValuedProjector C x :=
  (hC x).choose_spec.left

/-- The chosen projection point is a best approximation. -/
theorem projectionPoint_isBestApproximation (C : Set X) (hC : IsChebyshev C) (x : X) :
    IsBestApproximation x C (projectionPoint C hC x) :=
  projectionPoint_mem_setValuedProjector C hC x

/-- The chosen projection point lies in the Chebyshev set. -/
@[simp] theorem projectionPoint_mem (C : Set X) (hC : IsChebyshev C) (x : X) :
    projectionPoint C hC x ∈ C :=
  (projectionPoint_isBestApproximation C hC x).1

/-- In a Chebyshev set, any best approximation of `x` coincides with the chosen projection point.
-/
theorem eq_projectionPoint_of_isBestApproximation (C : Set X) (hC : IsChebyshev C) {x p : X}
    (hp : IsBestApproximation x C p) : p = projectionPoint C hC x :=
  (hC x).unique hp (projectionPoint_isBestApproximation C hC x)

/-- For a Chebyshev set, the projector is the single-valued specialization of the set-valued
projector, with codomain restricted to `C`. -/
noncomputable def projector (C : Set X) (hC : IsChebyshev C) : X → C :=
  fun x ↦ ⟨projectionPoint C hC x, projectionPoint_mem C hC x⟩

/-- The value of the projector is a best approximation to the original point. -/
theorem projector_isBestApproximation (C : Set X) (hC : IsChebyshev C) (x : X) :
    IsBestApproximation x C (projector C hC x : X) :=
  projectionPoint_isBestApproximation C hC x

/-! Source item: Chap03/Remark_3_11_1 -/

variable {X : Type u} [MetricSpace X]

/-- Helper for Remark 3.11.1: if a closure point admits a best approximation in `C`, then that
best approximation must coincide with the point, so the point already lies in `C`. -/
private lemma mem_of_mem_closure_of_isBestApproximation {C : Set X} {x p : X}
    (hx : x ∈ closure C) (hp : IsBestApproximation x C p) : x ∈ C := by
  -- A closure point has zero distance to the set, so the chosen best approximation is at distance
  -- zero from the point.
  have hxp_dist : dist x p = 0 := by
    rw [hp.2, Metric.infDist_zero_of_mem_closure hx]
  -- Zero distance identifies the point with its best approximation.
  have hxp : x = p := dist_eq_zero.mp hxp_dist
  simpa [hxp] using hp.1

/-- Helper for Remark 3.11.1: proximinality forces `closure C ⊆ C`. -/
private lemma closure_subset_of_isProximinalIn {C : Set X} (hC : IsProximinalIn C) :
    closure C ⊆ C := by
  intro x hx
  -- Choose a best approximation for the closure point and apply the zero-distance argument.
  obtain ⟨p, hp, hbest⟩ := hC x
  exact mem_of_mem_closure_of_isBestApproximation hx ⟨hp, hbest⟩

-- Proof sketch: if `x ∈ closure C`, then `Metric.infDist x C = 0`; a best approximation
-- `p ∈ C` must therefore satisfy `dist x p = 0`, hence `x = p ∈ C`.
/-- Remark 3.11.1: a proximinal set in a metric space is closed. -/
theorem isClosed_of_isProximinalIn {C : Set X} (hC : IsProximinalIn C) : IsClosed C := by
  -- The source proof reduces closedness to the invariant `closure C ⊆ C`.
  exact (closure_subset_iff_isClosed).mp
    (closure_subset_of_isProximinalIn hC)

/-- Every Chebyshev set in a metric space is closed. -/
theorem isClosed_of_isChebyshev {C : Set X} (hC : IsChebyshev C) : IsClosed C := by
  -- Forget uniqueness and reuse the proximal case proved above.
  exact isClosed_of_isProximinalIn fun x ↦ ExistsUnique.exists (hC x)

/-! Source item: Chap03/Remark_3_11_2 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Helper for Remark 3.11.2: the orthogonal projection minimizes the distance to the
finite-dimensional subspace among all comparison points in that subspace. -/
private lemma orthogonalProjection_dist_le (C : Submodule ℝ 𝓗)
    [FiniteDimensional ℝ C] (x : 𝓗) {c : 𝓗} (hc : c ∈ (C : Set 𝓗)) :
    dist x (C.orthogonalProjection x : 𝓗) ≤ dist x c := by
  let p : 𝓗 := C.orthogonalProjection x
  have hp : p ∈ (C : Set 𝓗) := by
    exact (C.orthogonalProjection x).property
  -- The residual `x - p` is orthogonal to `C`, so it is orthogonal to every competitor direction.
  have hperp : x - p ∈ Cᗮ := by
    change x - C.starProjection x ∈ Cᗮ
    simp
  have hpc : p - c ∈ C := by
    exact Submodule.sub_mem C hp hc
  have hinner : inner ℝ (x - p) (p - c) = 0 :=
    Submodule.inner_left_of_mem_orthogonal hpc hperp
  -- Pythagoras compares the squared distances once `x - c` is decomposed into orthogonal pieces.
  have hsq : ‖x - p + (p - c)‖ ^ 2 = ‖x - p‖ ^ 2 + ‖p - c‖ ^ 2 := by
    simpa [pow_two] using
      (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x - p) (p - c) hinner)
  have hdistsq : dist x c ^ 2 = dist x p ^ 2 + ‖p - c‖ ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm, ← sub_add_sub_cancel x p c, hsq]
  have hnonneg : 0 ≤ ‖p - c‖ ^ 2 := by
    positivity
  have hpnonneg : 0 ≤ dist x p := dist_nonneg
  have hcnonneg : 0 ≤ dist x c := dist_nonneg
  nlinarith [hdistsq, hnonneg, hpnonneg, hcnonneg]

/-- Helper for Remark 3.11.2: the orthogonal projection is a best approximation in the canonical
`IsBestApproximation` API. -/
private theorem orthogonalProjection_isBestApproximation (C : Submodule ℝ 𝓗)
    [FiniteDimensional ℝ C] (x : 𝓗) :
    IsBestApproximation x (C : Set 𝓗) (C.orthogonalProjection x : 𝓗) := by
  rw [isBestApproximation_iff_mem_and_dist_eq_infDist]
  constructor
  · exact (C.orthogonalProjection x).property
  · refine le_antisymm ?_ (Metric.infDist_le_dist_of_mem (C.orthogonalProjection x).property)
    exact (Metric.le_infDist ⟨(C.orthogonalProjection x : 𝓗), (C.orthogonalProjection x).property⟩).2
      fun y hy ↦ orthogonalProjection_dist_le C x hy

/-- Helper for Remark 3.11.2: any point of the subspace that realizes the infimal distance must
coincide with the orthogonal projection. -/
private lemma bestApproximation_eq_orthogonalProjection (C : Submodule ℝ 𝓗)
    [FiniteDimensional ℝ C] {x q : 𝓗} (hq : q ∈ (C : Set 𝓗))
    (hqdist : dist x q = Metric.infDist x (C : Set 𝓗)) :
    q = (C.orthogonalProjection x : 𝓗) := by
  let p : 𝓗 := C.orthogonalProjection x
  have hp : p ∈ (C : Set 𝓗) := by
    exact (C.orthogonalProjection x).property
  have hpdist : dist x p = Metric.infDist x (C : Set 𝓗) := by
    simpa [p] using
      (isBestApproximation_iff_mem_and_dist_eq_infDist x (C : Set 𝓗) (C.orthogonalProjection x : 𝓗)).1
        (orthogonalProjection_isBestApproximation C x) |>.2
  have hdist : dist x q = dist x p := by
    rw [hqdist, hpdist]
  -- Reuse the same orthogonal decomposition, now with `q` as another minimizing point.
  have hperp : x - p ∈ Cᗮ := by
    change x - C.starProjection x ∈ Cᗮ
    simp
  have hpq : p - q ∈ C := by
    exact Submodule.sub_mem C hp hq
  have hinner : inner ℝ (x - p) (p - q) = 0 :=
    Submodule.inner_left_of_mem_orthogonal hpq hperp
  have hsq : ‖x - p + (p - q)‖ ^ 2 = ‖x - p‖ ^ 2 + ‖p - q‖ ^ 2 := by
    simpa [pow_two] using
      (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x - p) (p - q) hinner)
  have hdistsq : dist x q ^ 2 = dist x p ^ 2 + ‖p - q‖ ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm, ← sub_add_sub_cancel x p q, hsq]
  have hsamedist : dist x q ^ 2 = dist x p ^ 2 := by
    rw [hdist]
  have hnormsq : ‖p - q‖ ^ 2 = 0 := by
    nlinarith [hdistsq, hsamedist, sq_nonneg ‖p - q‖]
  have hnorm : ‖p - q‖ = 0 := by
    nlinarith
  have hpqeq : p - q = 0 := norm_eq_zero.mp hnorm
  simpa [p] using (sub_eq_zero.mp hpqeq).symm

/-- Helper for Remark 3.11.2: orthogonal projection is the unique best approximation in the
finite-dimensional subspace. -/
private theorem eq_orthogonalProjection_of_isBestApproximation (C : Submodule ℝ 𝓗)
    [FiniteDimensional ℝ C] {x q : 𝓗} (hq : IsBestApproximation x (C : Set 𝓗) q) :
    q = (C.orthogonalProjection x : 𝓗) := by
  exact bestApproximation_eq_orthogonalProjection C hq.1 hq.2

-- Proof sketch: finite-dimensional subspaces are complete, hence admit orthogonal projections.
-- For each `x`, take `p := (C.orthogonalProjection x : 𝓗)`. The residual `x - p` is orthogonal to
-- `C`, so the Pythagorean identity shows `p` realizes `Metric.infDist x (C : Set 𝓗)`. Uniqueness
-- follows because two minimizers differ by a vector of `C` orthogonal to itself.
/-- Remark 3.11.2: every finite-dimensional linear subspace of a real Hilbert space admits a unique
best approximation to each point of the ambient space. -/
theorem finiteDimensionalSubspace_has_unique_best_approximations [CompleteSpace 𝓗]
    (C : Submodule ℝ 𝓗) [FiniteDimensional ℝ C] :
    IsChebyshev (C : Set 𝓗) := by
  intro x
  refine ⟨C.orthogonalProjection x, orthogonalProjection_isBestApproximation C x, ?_⟩
  -- Any other minimizing point must equal the orthogonal projection by the uniqueness helper.
  intro q hq
  exact eq_orthogonalProjection_of_isBestApproximation C hq

/-! Source item: Chap03/Example_3_13 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Helper for Example 3.13: distinct scaled orthonormal vectors stay at distance strictly bigger
than `1`. -/
private lemma scaled_orthonormal_dist_gt_one_of_ne (e : ℕ → 𝓗) (he : Orthonormal ℝ e)
    (α : ℕ → ℝ)
    (hα_gt_one : ∀ n : ℕ, 1 < α n) {m n : ℕ} (hmn : m ≠ n) :
    1 < dist (α m • e m) (α n • e n) := by
  -- Expand the squared norm and simplify the orthonormal cross-term away.
  have hαm_pos : 0 < α m := lt_trans zero_lt_one (hα_gt_one m)
  have hαn_pos : 0 < α n := lt_trans zero_lt_one (hα_gt_one n)
  have hm : ‖α m • e m‖ = α m := by
    rw [norm_smul, he.norm_eq_one m, mul_one, Real.norm_of_nonneg hαm_pos.le]
  have hn : ‖α n • e n‖ = α n := by
    rw [norm_smul, he.norm_eq_one n, mul_one, Real.norm_of_nonneg hαn_pos.le]
  have hinner : inner ℝ (α m • e m) (α n • e n) = 0 := by
    rw [real_inner_smul_left, inner_smul_right, he.inner_eq_zero hmn, mul_zero, mul_zero]
  have hsq :
      dist (α m • e m) (α n • e n) ^ 2 = α m ^ 2 + α n ^ 2 := by
    rw [dist_eq_norm, norm_sub_sq_real, hm, hn, hinner]
    ring
  have hnonneg : 0 ≤ dist (α m • e m) (α n • e n) := dist_nonneg
  nlinarith [hsq, hα_gt_one m, hα_gt_one n]

/-- Helper for Example 3.13: the distance from `0` to a scaled orthonormal vector is the scaling
coefficient. -/
private lemma dist_zero_scaled_orthonormal_point (e : ℕ → 𝓗) (he : Orthonormal ℝ e)
    (α : ℕ → ℝ)
    (hα_gt_one : ∀ n : ℕ, 1 < α n) (n : ℕ) :
    dist (0 : 𝓗) (α n • e n) = α n := by
  -- The norm is `|α n| · ‖e n‖`, and positivity of `α n` removes the absolute value.
  have hαn_pos : 0 < α n := lt_trans zero_lt_one (hα_gt_one n)
  rw [dist_eq_norm, zero_sub, norm_neg, norm_smul, he.norm_eq_one n, mul_one,
    Real.norm_of_nonneg hαn_pos.le]

/-- Helper for Example 3.13: a convergent sequence in the scaled orthonormal range is eventually
constant. -/
private lemma eventually_constant_of_tendsto_scaled_orthonormal_range (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) (α : ℕ → ℝ) (hα_gt_one : ∀ n : ℕ, 1 < α n) {u : ℕ → 𝓗} {x : 𝓗}
    (hu : ∀ n : ℕ, u n ∈ Set.range (fun k ↦ α k • e k)) (hx : Tendsto u atTop (𝓝 x)) :
    ∃ N k, ∀ n ≥ N, u n = α k • e k := by
  -- Convergent sequences are Cauchy, so eventually all later terms lie within distance `< 1`
  -- of a fixed anchor term.
  have hcauchy : CauchySeq u := hx.cauchySeq
  rcases (Metric.cauchySeq_iff'.1 hcauchy) 1 zero_lt_one with ⟨N, hN⟩
  rcases Set.mem_range.1 (hu N) with ⟨k, hk⟩
  refine ⟨N, k, ?_⟩
  intro n hn
  rcases Set.mem_range.1 (hu n) with ⟨kn, hkn⟩
  by_contra hneq
  have hdist_lt : dist (u n) (u N) < 1 := hN n hn
  have hkne : kn ≠ k := by
    intro hEq
    apply hneq
    calc
      u n = α kn • e kn := hkn.symm
      _ = α k • e k := by simp [hEq]
  have hdist_gt : 1 < dist (u n) (u N) := by
    rw [← hkn, ← hk]
    exact scaled_orthonormal_dist_gt_one_of_ne e he α hα_gt_one hkne
  linarith

/-- If every coefficient `α n` is strictly bigger than `1`, then the scaled orthonormal range is
closed. This is the separation statement used in Example 3.13 (1). -/
theorem isClosed_scaled_orthonormal_range_of_one_lt (e : ℕ → 𝓗) (he : Orthonormal ℝ e)
    (α : ℕ → ℝ) (hα_gt_one : ∀ n : ℕ, 1 < α n) :
    IsClosed (Set.range (fun n ↦ α n • e n)) := by
  -- The separation lemma makes every convergent sequence in the set eventually constant.
  have hseqClosed : IsSeqClosed (Set.range (fun n ↦ α n • e n)) := by
    intro u x hu hx
    rcases eventually_constant_of_tendsto_scaled_orthonormal_range e he α hα_gt_one hu hx with
      ⟨N, k, hNk⟩
    have hconst : u =ᶠ[atTop] fun _ ↦ α k • e k := by
      exact Filter.eventually_atTop.2 ⟨N, fun n hn ↦ hNk n hn⟩
    have hxconst : Tendsto (fun _ : ℕ ↦ α k • e k) atTop (𝓝 x) := hx.congr' hconst
    have hxeq : x = α k • e k := tendsto_nhds_unique hxconst tendsto_const_nhds
    exact Set.mem_range.2 ⟨k, hxeq.symm⟩
  exact (isSeqClosed_iff_isClosed.1 hseqClosed)

-- Proof sketch: Example 3.13 (1) is an immediate corollary of
-- `isClosed_scaled_orthonormal_range_of_one_lt`.
/-- Example 3.13 (1): if `e` is orthonormal and `α n > 1` decreases to `1`, then the set
`{α n • e n | n : ℕ}` is closed. -/
theorem isClosed_scaled_orthonormal_range (e : ℕ → 𝓗) (he : Orthonormal ℝ e) (α : ℕ → ℝ)
    (hα_gt_one : ∀ n : ℕ, 1 < α n) (_hα_antitone : Antitone α)
    (_hα_tendsto : Tendsto α atTop (nhds 1)) :
    IsClosed (Set.range (fun n ↦ α n • e n)) :=
  isClosed_scaled_orthonormal_range_of_one_lt e he α hα_gt_one

-- Proof sketch: the norms of the points `α n • e n` are exactly `α n`, so `hα_tendsto` gives
-- `Metric.infDist 0 (Set.range (fun n ↦ α n • e n)) = 1`; since every point of the set has norm
-- strictly bigger than `1` by `hα_gt_one`, no point of the set realizes this infimum.
/-- The distance from `0` to `Set.range (fun n ↦ α n • e n)` is `1` whenever `α n > 1` tends to
`1`. -/
theorem zero_infDist_scaled_orthonormal_range_eq_one_of_tendsto (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) (α : ℕ → ℝ) (hα_gt_one : ∀ n : ℕ, 1 < α n)
    (hα_tendsto : Tendsto α atTop (nhds 1)) :
    Metric.infDist (0 : 𝓗) (Set.range (fun n ↦ α n • e n)) = 1 := by
  let C : Set 𝓗 := Set.range (fun n ↦ α n • e n)
  have hC_nonempty : C.Nonempty := ⟨α 0 • e 0, by
    simp [C]⟩
  have hlower : 1 ≤ Metric.infDist (0 : 𝓗) C := by
    -- Every point in the set has norm strictly bigger than `1`.
    rw [Metric.le_infDist hC_nonempty]
    intro y hy
    rcases Set.mem_range.1 hy with ⟨n, rfl⟩
    rw [dist_zero_scaled_orthonormal_point e he α hα_gt_one n]
    exact le_of_lt (hα_gt_one n)
  have hupper : Metric.infDist (0 : 𝓗) C ≤ 1 := by
    -- Since `α n → 1`, the set contains points whose distance to `0` is arbitrarily close to `1`.
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    rcases (Metric.tendsto_atTop.1 hα_tendsto) ε hε with ⟨N, hN⟩
    have hdist : dist (α N) 1 < ε := hN N le_rfl
    have hα_lt : α N < 1 + ε := by
      have hsub : α N - 1 < ε := by
        simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (le_of_lt (hα_gt_one N)))] using hdist
      linarith
    have hmem : α N • e N ∈ C := by
      simp [C]
    calc
      Metric.infDist (0 : 𝓗) C ≤ dist (0 : 𝓗) (α N • e N) := Metric.infDist_le_dist_of_mem hmem
      _ = α N := dist_zero_scaled_orthonormal_point e he α hα_gt_one N
      _ ≤ 1 + ε := le_of_lt hα_lt
  exact le_antisymm hupper hlower

/-- Example 3.13 uses the previous infimum computation under the stronger textbook hypothesis that
`α` decreases to `1`. -/
theorem zero_infDist_scaled_orthonormal_range_eq_one (e : ℕ → 𝓗) (he : Orthonormal ℝ e)
    (α : ℕ → ℝ) (hα_gt_one : ∀ n : ℕ, 1 < α n) (_hα_antitone : Antitone α)
    (hα_tendsto : Tendsto α atTop (nhds 1)) :
    Metric.infDist (0 : 𝓗) (Set.range (fun n ↦ α n • e n)) = 1 :=
  zero_infDist_scaled_orthonormal_range_eq_one_of_tendsto e he α hα_gt_one hα_tendsto

-- Proof sketch: combine `zero_infDist_scaled_orthonormal_range_eq_one` with the characterization
-- of best approximations from `Definition 3.8`; any best approximation `p = α n • e n` would
-- satisfy `‖p‖ = 1`, contradicting `1 < α n`.
/-- If `α n > 1` tends to `1`, then `0` has no best approximation in the scaled orthonormal
range. -/
theorem zero_has_no_projection_onto_scaled_orthonormal_range_of_tendsto (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) (α : ℕ → ℝ) (hα_gt_one : ∀ n : ℕ, 1 < α n)
    (hα_tendsto : Tendsto α atTop (nhds 1)) :
    ¬ ∃ p : 𝓗, IsBestApproximation (0 : 𝓗) (Set.range (fun n ↦ α n • e n)) p := by
  -- A best approximation would have to realize the infimum distance `1`, but every point in the
  -- set has distance strictly bigger than `1`.
  rintro ⟨p, hp⟩
  rw [isBestApproximation_iff_mem_and_dist_eq_infDist] at hp
  rcases Set.mem_range.1 hp.1 with ⟨n, rfl⟩
  have hdist : dist (0 : 𝓗) (α n • e n) = α n :=
    dist_zero_scaled_orthonormal_point e he α hα_gt_one n
  have hinf : Metric.infDist (0 : 𝓗) (Set.range (fun k ↦ α k • e k)) = 1 :=
    zero_infDist_scaled_orthonormal_range_eq_one_of_tendsto e he α hα_gt_one hα_tendsto
  have hα_eq_one : α n = 1 := by
    calc
      α n = dist (0 : 𝓗) (α n • e n) := hdist.symm
      _ = Metric.infDist (0 : 𝓗) (Set.range (fun k ↦ α k • e k)) := hp.2
      _ = 1 := hinf
  linarith [hα_gt_one n]

/-- Example 3.13 (2): `0` has no projection onto `{α n • e n | n : ℕ}`; equivalently, the
distance from `0` to this set is not attained on the set. -/
theorem zero_has_no_projection_onto_scaled_orthonormal_range (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) (α : ℕ → ℝ) (hα_gt_one : ∀ n : ℕ, 1 < α n)
    (_hα_antitone : Antitone α) (hα_tendsto : Tendsto α atTop (nhds 1)) :
    ¬ ∃ p : 𝓗, IsBestApproximation (0 : 𝓗) (Set.range (fun n ↦ α n • e n)) p :=
  zero_has_no_projection_onto_scaled_orthonormal_range_of_tendsto
    e he α hα_gt_one hα_tendsto

/-! Source item: Chap03/Proposition_3_12 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
  [FiniteDimensional ℝ 𝓗]

/-- Helper for Proposition 3.12: the norm of the projection is controlled by the distance to the
set and the norm of the original point. -/
private lemma norm_projectionPoint_le_infDist_add_norm {X : Type u} [NormedAddCommGroup X]
    {C : Set X} (hC : IsChebyshev C) (x : X) :
    ‖projectionPoint C hC x‖ ≤ Metric.infDist x C + ‖x‖ := by
  -- Rewrite the projector as `(P_C x - x) + x` and apply the triangle inequality.
  calc
    ‖projectionPoint C hC x‖ = ‖(projectionPoint C hC x - x) + x‖ := by
      simp [sub_eq_add_neg, add_assoc]
    _ ≤ ‖projectionPoint C hC x - x‖ + ‖x‖ := norm_add_le _ _
    _ = dist x (projectionPoint C hC x) + ‖x‖ := by
      rw [dist_eq_norm, norm_sub_rev]
    _ = Metric.infDist x C + ‖x‖ := by
      rw [(projectionPoint_isBestApproximation C hC x).2]

/-- Helper for Proposition 3.12: any subsequential limit of projection points is a best
approximation to the ambient limit point. -/
  private lemma isBestApproximation_of_tendsto_projection_subsequence {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] {C : Set H} (hC : IsChebyshev C)
    {u : ℕ → H} {x y : H} (hu : Tendsto u atTop (nhds x))
    (hy : Tendsto (fun n ↦ projectionPoint C hC (u n)) atTop (nhds y)) :
    y ∈ C ∧ dist x y = Metric.infDist x C := by
  have hclosed : IsClosed C := by
    exact isClosed_of_isChebyshev hC
  have hy_mem : y ∈ C := by
    -- Every term of the projection sequence lies in `C`, and `C` is closed.
    exact hclosed.mem_of_tendsto hy (Filter.Eventually.of_forall fun n =>
      projectionPoint_mem C hC (u n))
  have hdist_proj :
      Tendsto (fun n ↦ dist (u n) (projectionPoint C hC (u n))) atTop (nhds (dist x y)) := by
    -- Distance is continuous in both variables, so it passes to the joint limit.
    exact (continuous_fst.dist continuous_snd).tendsto (x, y) |>.comp (hu.prodMk_nhds hy)
  have hinfDist :
      Tendsto (fun n ↦ Metric.infDist (u n) C) atTop (nhds (Metric.infDist x C)) := by
    -- The distance-to-set function is continuous.
    exact (Metric.continuous_infDist_pt C).tendsto x |>.comp hu
  have hdist_inf :
      Tendsto (fun n ↦ dist (u n) (projectionPoint C hC (u n))) atTop
        (nhds (Metric.infDist x C)) := by
    -- Each term realizes the distance to `C`.
    exact Tendsto.congr' (Filter.Eventually.of_forall fun n =>
      ((projectionPoint_isBestApproximation C hC (u n)).2).symm) hinfDist
  exact ⟨hy_mem, tendsto_nhds_unique hdist_proj hdist_inf⟩

/-- Proposition 3.12: in a finite-dimensional real Hilbert space, the metric projection point map
onto a Chebyshev set is continuous. -/
theorem continuous_projectionPoint_of_isChebyshev {C : Set 𝓗} (hC : IsChebyshev C) :
    Continuous (projectionPoint C hC) := by
  -- Route correction: the proof works by sequential compactness of bounded projection subsequences,
  -- not by trying to prove a direct Lipschitz estimate for an arbitrary Chebyshev set.
  refine (continuous_iff_seqContinuous).2 ?_
  intro u x hu
  -- It suffices to show that every subsequence of the projection sequence has a further
  -- subsubsequence converging to the desired limit.
  refine tendsto_of_subseq_tendsto ?_
  intro ns hns
  have hu_sub : Tendsto (fun n ↦ u (ns n)) atTop (nhds x) := hu.comp hns
  have hu_bdd : IsBounded (Set.range fun n ↦ u (ns n)) :=
    Metric.isBounded_range_of_tendsto _ hu_sub
  have hd_bdd : IsBounded (Set.range fun n ↦ Metric.infDist (u (ns n)) C) :=
    Metric.isBounded_range_of_tendsto _ <|
      ((Metric.continuous_infDist_pt C).tendsto x).comp hu_sub
  obtain ⟨Ru, hRu_pos, hRu⟩ := hu_bdd.subset_closedBall_lt 0 (0 : 𝓗)
  obtain ⟨Rd, hRd_pos, hRd⟩ := hd_bdd.subset_closedBall_lt 0 (0 : ℝ)
  let R : ℝ := Rd + Ru
  have hproj_mem :
      ∀ n, projectionPoint C hC (u (ns n)) ∈ Metric.closedBall (0 : 𝓗) R := by
    intro n
    have hu_norm : ‖u (ns n)‖ ≤ Ru := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hRu (by exact ⟨n, rfl⟩)
    have hd_le : Metric.infDist (u (ns n)) C ≤ Rd := by
      have hd_abs : |Metric.infDist (u (ns n)) C| ≤ Rd := by
        simpa [Metric.mem_closedBall, Real.dist_eq] using hRd (by exact ⟨n, rfl⟩)
      simpa [abs_of_nonneg (Metric.infDist_nonneg)] using hd_abs
    have hproj_norm :
        ‖projectionPoint C hC (u (ns n))‖ ≤ R := by
      calc
        ‖projectionPoint C hC (u (ns n))‖
            ≤ Metric.infDist (u (ns n)) C + ‖u (ns n)‖ :=
          norm_projectionPoint_le_infDist_add_norm hC (u (ns n))
        _ ≤ Rd + Ru := add_le_add hd_le hu_norm
        _ = R := rfl
    simpa [R, Metric.mem_closedBall, dist_eq_norm] using hproj_norm
  obtain ⟨y, _hy_closure, φ, hφmono, hφtendsto⟩ :=
    tendsto_subseq_of_bounded Metric.isBounded_closedBall hproj_mem
  have hu_subsub : Tendsto (fun n ↦ u (ns (φ n))) atTop (nhds x) :=
    hu_sub.comp hφmono.tendsto_atTop
  have hy_best :
      y ∈ C ∧ dist x y = Metric.infDist x C := by
    -- The subsubsequence limit remains a best approximation of `x`.
    simpa [Function.comp_def] using
      isBestApproximation_of_tendsto_projection_subsequence hC hu_subsub hφtendsto
  have hy_eq : y = projectionPoint C hC x :=
    eq_projectionPoint_of_isBestApproximation C hC hy_best
  refine ⟨φ, ?_⟩
  -- Uniqueness of the best approximation identifies every cluster point with `P_C x`.
  simpa [Function.comp_def, hy_eq] using hφtendsto

/-- Compatibility reformulation of Proposition 3.12 for the subtype-valued projector. -/
theorem continuous_projector_of_isChebyshev {C : Set 𝓗} (hC : IsChebyshev C) :
    Continuous (projector C hC) := by
  -- First prove continuity of the ambient projection point map.
  have hcont : Continuous (projectionPoint C hC) :=
    continuous_projectionPoint_of_isChebyshev hC
  -- Then package the continuous ambient map into the subtype-valued projector.
  simpa [projector] using hcont.subtype_mk (projectionPoint_mem C hC)

/-! Source item: Chap03/Proposition_3_14 -/


noncomputable section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

/-- Helper for Proposition 3.14: the weak image of a norm-closed ball in a real Hilbert space is
compact. -/
private lemma weak_image_closedBall_isCompact {x : 𝓗} {r : ℝ} (hr : 0 ≤ r) :
    IsCompact ((toWeakSpace ℝ 𝓗) '' Metric.closedBall x r : Set (WeakSpace ℝ 𝓗)) := by
  -- First compactify the scaled unit ball using the earlier weak-compactness theorem.
  have hscaled :
      IsCompact ((toWeakSpace ℝ 𝓗) '' (r • {u : 𝓗 | ‖u‖ ≤ 1}) : Set (WeakSpace ℝ 𝓗)) :=
    isCompact_weakImage_smul_unit_ball r
  -- Then translate the compact weak image by the fixed center `x`.
  have htranslate :
      IsCompact
        ((fun w : WeakSpace ℝ 𝓗 ↦ toWeakSpace ℝ 𝓗 x + w) ''
          ((toWeakSpace ℝ 𝓗) '' (r • {u : 𝓗 | ‖u‖ ≤ 1}) : Set (WeakSpace ℝ 𝓗))) :=
    hscaled.image (continuous_const.add continuous_id)
  -- The geometric identity `closedBall x r = x + r • closedBall 0 1` aligns the sets.
  convert htranslate using 1
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← affinity_unitClosedBall hr x] at hy
    rcases Set.mem_vadd_set.mp hy with ⟨v, hv, hvEq⟩
    rcases hv with ⟨u, huBall, rfl⟩
    refine ⟨toWeakSpace ℝ 𝓗 (r • u), ?_, ?_⟩
    · refine ⟨r • u, ?_, rfl⟩
      refine ⟨u, ?_, rfl⟩
      simpa [Metric.mem_closedBall, dist_eq_norm] using huBall
    · simpa [hvEq, add_comm, add_left_comm, add_assoc]
  · rintro ⟨w, hw, hz⟩
    rcases hw with ⟨v, hv, rfl⟩
    rcases hv with ⟨u, hu, rfl⟩
    refine ⟨x + r • u, ?_, ?_⟩
    · rw [← affinity_unitClosedBall hr x]
      apply Set.mem_vadd_set.mpr
      refine ⟨r • u, ?_, by simp⟩
      exact ⟨u, by simpa [Metric.mem_closedBall, dist_eq_norm] using hu, rfl⟩
    · simpa [add_comm, add_left_comm, add_assoc] using hz

omit [CompleteSpace 𝓗] in
/-- Helper for Proposition 3.14: the weak image commutes with intersecting a set with a closed
ball. -/
private lemma weak_image_inter_closedBall_eq {C : Set 𝓗} {x : 𝓗} {r : ℝ} :
    ((toWeakSpace ℝ 𝓗) '' (C ∩ Metric.closedBall x r) : Set (WeakSpace ℝ 𝓗)) =
      ((toWeakSpace ℝ 𝓗) '' C) ∩ ((toWeakSpace ℝ 𝓗) '' Metric.closedBall x r) := by
  -- Injectivity of `toWeakSpace` lets us identify the two witnesses in the intersection.
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz.1, rfl⟩, ⟨z, hz.2, rfl⟩⟩
  · rintro ⟨hyC, hyB⟩
    rcases hyC with ⟨z, hzC, hzEq⟩
    rcases hyB with ⟨w, hwB, hwEq⟩
    have hzw : z = w := (toWeakSpace ℝ 𝓗).injective (hzEq.trans hwEq.symm)
    exact ⟨z, ⟨hzC, hzw ▸ hwB⟩, hzEq⟩

/-- Helper for Proposition 3.14: the distance to a fixed point is lower semicontinuous for the weak
topology on a real Hilbert space. -/
private lemma weak_dist_lowerSemicontinuous (x : 𝓗) :
    LowerSemicontinuous (fun y : WeakSpace ℝ 𝓗 ↦ dist x ((toWeakSpace ℝ 𝓗).symm y)) := by
  -- Rewrite the distance as the supremum of weakly continuous coordinate functionals on the weak
  -- closed unit ball.
  have hrepr :
      (fun y : WeakSpace ℝ 𝓗 ↦ dist x ((toWeakSpace ℝ 𝓗).symm y)) =
        fun y : WeakSpace ℝ 𝓗 ↦
          ⨆ u : weakClosedUnitBall 𝓗,
            |inner ℝ ((toWeakSpace ℝ 𝓗).symm u) (x - ((toWeakSpace ℝ 𝓗).symm y))| := by
    funext y
    calc
      dist x ((toWeakSpace ℝ 𝓗).symm y) = ‖x - ((toWeakSpace ℝ 𝓗).symm y)‖ := by
        rw [dist_eq_norm]
      _ = ‖evalOnWeakClosedUnitBall 𝓗 (x - ((toWeakSpace ℝ 𝓗).symm y))‖ := by
        rw [evalOnWeakClosedUnitBall_norm_eq (x - ((toWeakSpace ℝ 𝓗).symm y))]
      _ = ⨆ u : weakClosedUnitBall 𝓗,
            ‖evalOnWeakClosedUnitBall 𝓗 (x - ((toWeakSpace ℝ 𝓗).symm y)) u‖ := by
        rw [ContinuousMap.norm_eq_iSup_norm]
      _ = ⨆ u : weakClosedUnitBall 𝓗,
            |inner ℝ ((toWeakSpace ℝ 𝓗).symm u) (x - ((toWeakSpace ℝ 𝓗).symm y))| := by
        rfl
  rw [hrepr]
  -- Each coordinate is continuous, so the pointwise supremum is lower semicontinuous.
  refine lowerSemicontinuous_ciSup ?_ ?_
  · intro y
    refine ⟨‖x - ((toWeakSpace ℝ 𝓗).symm y)‖, ?_⟩
    rintro _ ⟨u, rfl⟩
    calc
      |inner ℝ ((toWeakSpace ℝ 𝓗).symm u) (x - ((toWeakSpace ℝ 𝓗).symm y))|
          ≤ ‖(toWeakSpace ℝ 𝓗).symm u‖ * ‖x - ((toWeakSpace ℝ 𝓗).symm y)‖ :=
            abs_real_inner_le_norm _ _
      _ ≤ 1 * ‖x - ((toWeakSpace ℝ 𝓗).symm y)‖ := by
        gcongr
        exact weakClosedUnitBall_norm_le_one u
      _ = ‖x - ((toWeakSpace ℝ 𝓗).symm y)‖ := by ring
  · intro u
    have hycont :
        Continuous fun y : WeakSpace ℝ 𝓗 ↦
          inner ℝ ((toWeakSpace ℝ 𝓗).symm u) ((toWeakSpace ℝ 𝓗).symm y) := by
      simpa [real_inner_comm] using
        (weakSpace_continuous_inner_right ((toWeakSpace ℝ 𝓗).symm u))
    have hcoord :
        Continuous fun y : WeakSpace ℝ 𝓗 ↦
          inner ℝ ((toWeakSpace ℝ 𝓗).symm u) x -
            inner ℝ ((toWeakSpace ℝ 𝓗).symm u) ((toWeakSpace ℝ 𝓗).symm y) :=
      continuous_const.sub hycont
    have habsEq :
        (fun y : WeakSpace ℝ 𝓗 ↦
          |inner ℝ ((toWeakSpace ℝ 𝓗).symm u) (x - ((toWeakSpace ℝ 𝓗).symm y))|) =
        (fun y : WeakSpace ℝ 𝓗 ↦
          |inner ℝ ((toWeakSpace ℝ 𝓗).symm u) x -
            inner ℝ ((toWeakSpace ℝ 𝓗).symm u) ((toWeakSpace ℝ 𝓗).symm y)|) := by
      funext y
      rw [inner_sub_right]
    rw [habsEq]
    exact (Continuous.abs hcoord).lowerSemicontinuous

omit [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗] in
/-- Helper for Proposition 3.14: a minimizer on the truncation `C ∩ closedBall x (dist x z)` is
already a global minimizer on `C`. -/
private lemma truncated_minimizer_le_all {C : Set 𝓗} {x z p : 𝓗}
    (hp : p ∈ C ∩ Metric.closedBall x (dist x z))
    (hmin : ∀ y ∈ C ∩ Metric.closedBall x (dist x z), dist x p ≤ dist x y) :
    ∀ y ∈ C, dist x p ≤ dist x y := by
  intro y hyC
  by_cases hyBall : y ∈ Metric.closedBall x (dist x z)
  · -- Inside the truncating ball we can invoke the local minimizing property directly.
    exact hmin y ⟨hyC, hyBall⟩
  · -- Outside the truncating ball, the radius bound on `p` gives the desired comparison.
    have hp_le : dist x p ≤ dist x z := by
      simpa [Metric.mem_closedBall, dist_comm] using hp.2
    have hy_gt : dist x z < dist x y := by
      have hyBall' : ¬ dist x y ≤ dist x z := by
        simpa [Metric.mem_closedBall, dist_comm] using hyBall
      exact lt_of_not_ge hyBall'
    exact le_trans hp_le hy_gt.le

-- Proof sketch: fix `x : 𝓗` and intersect `C` with a sufficiently large
-- closed ball centered at `x`.
-- By weak closedness and the weak compactness of closed balls in a Hilbert space, this intersection
-- is weakly compact. The norm-distance function is weakly lower semicontinuous, so it attains its
-- minimum there; the minimizer is then a best approximation from `C`.
/-- Proposition 3.14: every nonempty weakly closed subset of a real Hilbert space is proximinal,
so every point admits a best approximation in the set. -/
theorem exists_bestApproximation_of_nonempty_weaklyClosed {C : Set 𝓗} (hC : C.Nonempty)
    (hweak : IsClosed ((toWeakSpace ℝ 𝓗) '' C)) :
    IsProximinalIn C := by
  rw [isProximinalIn_iff_forall_exists_bestApproximation]
  intro x
  rcases hC with ⟨z, hzC⟩
  let D : Set 𝓗 := C ∩ Metric.closedBall x (dist x z)
  have hzD : z ∈ D := by
    -- The chosen point `z ∈ C` lies in the truncating ball by construction.
    exact ⟨hzC, by simp [Metric.mem_closedBall, dist_comm]⟩
  have hcompactD :
      IsCompact ((toWeakSpace ℝ 𝓗) '' D : Set (WeakSpace ℝ 𝓗)) := by
    -- The truncation is a weakly closed subset of the weakly compact image of the closed ball.
    rw [show D = C ∩ Metric.closedBall x (dist x z) by rfl, weak_image_inter_closedBall_eq]
    exact (weak_image_closedBall_isCompact dist_nonneg).inter_left hweak
  have hdistD :
      LowerSemicontinuousOn
        (fun y : WeakSpace ℝ 𝓗 ↦ dist x ((toWeakSpace ℝ 𝓗).symm y))
        (((toWeakSpace ℝ 𝓗) '' D : Set (WeakSpace ℝ 𝓗))) :=
    (weak_dist_lowerSemicontinuous x).lowerSemicontinuousOn _
  obtain ⟨w, hwD, hwmin⟩ :=
    hdistD.exists_isMinOn (Set.Nonempty.image _ ⟨z, hzD⟩) hcompactD
  rcases hwD with ⟨p, hpD, rfl⟩
  refine ⟨p, ?_⟩
  have hminD : ∀ y ∈ D, dist x p ≤ dist x y := by
    -- Pull the weak-space minimizer back to the original Hilbert space.
    intro y hyD
    have hyImage : toWeakSpace ℝ 𝓗 y ∈ (toWeakSpace ℝ 𝓗) '' D := ⟨y, hyD, rfl⟩
    simpa using hwmin hyImage
  have hglobal : ∀ y ∈ C, dist x p ≤ dist x y := truncated_minimizer_le_all hpD hminD
  refine ⟨hpD.1, le_antisymm ?_ (Metric.infDist_le_dist_of_mem hpD.1)⟩
  rw [Metric.le_infDist ⟨p, hpD.1⟩]
  exact hglobal

end

/-! Source item: Chap03/Proposition_3_15_1 -/

-- Proof sketch: for each `x`, discard the uniqueness part of the Chebyshev hypothesis and keep
-- the realizing best approximation.
/-- Proposition 3.15.1: a Chebyshev set is proximinal. -/
theorem isProximinalIn_of_isChebyshev {X : Type u} [PseudoMetricSpace X] {C : Set X}
    (hC : IsChebyshev C) :
    IsProximinalIn C := by
  intro x
  exact ExistsUnique.exists (hC x)

/-! Source item: Chap03/Proposition_3_15_2 -/

variable {X : Type u} [MetricSpace X]

/- The interval `[-1,1]` in `ℝ` is nonempty. -/
private lemma neg_one_le_one : (-1 : ℝ) ≤ 1 := by
  norm_num

/- The horizontal segment `{(t,0) : t ∈ [-1,1]}` viewed inside `ULift (ℝ × ℝ)`. -/
private def horizontalSegment : Set (ULift.{u} (ℝ × ℝ)) :=
  {p | p.down.2 = 0 ∧ p.down.1 ∈ Set.Icc (-1 : ℝ) 1}

/- Clamp a real number to the interval `[-1,1]`. -/
private noncomputable def clampToSegment : ℝ → Set.Icc (-1 : ℝ) 1 :=
  Set.projIcc (-1 : ℝ) 1 neg_one_le_one

/- A point that is no farther than every point of `C` realizes `Metric.infDist x C`. -/
private lemma dist_eq_infDist_of_forall_le {Y : Type u} [MetricSpace Y] {C : Set Y} {x p : Y}
    (hp : p ∈ C) (hmin : ∀ q ∈ C, dist x p ≤ dist x q) :
    dist x p = Metric.infDist x C := by
  -- Convert the pointwise minimizing property into the defining infimum formula.
  apply le_antisymm
  · rw [Metric.infDist_eq_iInf]
    let _ : Nonempty {q // q ∈ C} := ⟨⟨p, hp⟩⟩
    exact le_ciInf (fun q : {q // q ∈ C} ↦ hmin q.1 q.2)
  · exact Metric.infDist_le_dist_of_mem hp

/- Clamping to `[-1,1]` minimizes the distance to any point of that interval. -/
private lemma abs_sub_projIcc_le_abs_sub_of_mem_Icc (x t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |x - ((clampToSegment x : Set.Icc (-1 : ℝ) 1) : ℝ)| ≤ |x - t| := by
  -- Split according to whether `x` lies to the left, inside, or to the right of the interval.
  by_cases hxleft : x ≤ -1
  · rw [clampToSegment, Set.projIcc_of_le_left neg_one_le_one hxleft]
    have hx_nonpos : x - (-1 : ℝ) ≤ 0 := by
      linarith
    have hxt_nonpos : x - t ≤ 0 := by
      linarith [ht.1, hxleft]
    rw [abs_of_nonpos hx_nonpos, abs_of_nonpos hxt_nonpos]
    linarith [ht.1]
  · by_cases hxright : 1 ≤ x
    · rw [clampToSegment, Set.projIcc_of_right_le neg_one_le_one hxright]
      have hx_nonneg : 0 ≤ x - (1 : ℝ) := by
        linarith
      have hxt_nonneg : 0 ≤ x - t := by
        linarith [ht.2, hxright]
      rw [abs_of_nonneg hx_nonneg, abs_of_nonneg hxt_nonneg]
      linarith [ht.2]
    · have hxmem : x ∈ Set.Icc (-1 : ℝ) 1 := by
        constructor
        · linarith
        · linarith
      rw [clampToSegment, Set.projIcc_of_mem neg_one_le_one hxmem]
      simp

/- Clamping the first coordinate and setting the second coordinate to zero gives a best
approximation from the horizontal segment. -/
private lemma horizontal_segment_projection_is_best (x : ULift.{u} (ℝ × ℝ)) :
    IsBestApproximation x horizontalSegment
      (ULift.up (((clampToSegment x.down.1 : Set.Icc (-1 : ℝ) 1) : ℝ), 0)) := by
  constructor
  · -- The clamped point lies on the segment by construction.
    constructor
    · rfl
    · exact (clampToSegment x.down.1).2
  · -- Rewrite the sup-norm distances and compare only the first coordinates.
    apply dist_eq_infDist_of_forall_le
    · constructor
      · rfl
      · exact (clampToSegment x.down.1).2
    · intro q hq
      rw [show dist x
          (ULift.up (((clampToSegment x.down.1 : Set.Icc (-1 : ℝ) 1) : ℝ), 0)) =
            dist x.down
              ((((clampToSegment x.down.1 : Set.Icc (-1 : ℝ) 1) : ℝ), 0) : ℝ × ℝ) by
          rfl]
      rw [show dist x q = dist x.down q.down by rfl]
      rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq, hq.1]
      have hclamp :
          |x.down.1 - ((clampToSegment x.down.1 : Set.Icc (-1 : ℝ) 1) : ℝ)| ≤
            |x.down.1 - q.down.1| := by
        exact abs_sub_projIcc_le_abs_sub_of_mem_Icc x.down.1 q.down.1 hq.2
      exact max_le_max hclamp le_rfl

/- Every point of the horizontal segment is at distance at least `1` from `(0,1)`. -/
private lemma one_le_dist_top_point_of_mem_horizontal_segment (q : ULift.{u} (ℝ × ℝ))
    (hq : q ∈ horizontalSegment) :
    1 ≤ dist (ULift.up ((0 : ℝ), 1)) q := by
  -- The second coordinate already contributes distance `1` everywhere on the segment.
  rw [show dist (ULift.up ((0 : ℝ), 1)) q = dist ((0 : ℝ), 1) q.down by rfl]
  rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, hq.1]
  norm_num

-- Proof sketch: take `X = ULift (ℝ × ℝ)` with the sup norm inherited from `ℝ × ℝ`, and let `C`
-- be the horizontal segment `{(t, 0) : t ∈ Set.Icc (-1) 1}`. For each `x`, clamp the first
-- coordinate to `[-1, 1]` to obtain a point of `C` realizing `Metric.infDist x C`, so `C` is
-- proximinal. For the point with coordinates `(0, 1)`, every point of the segment is at distance
-- `1`, yielding at least two distinct best approximations and therefore showing that `C` is not
-- Chebyshev.
/-- Proposition 3.15.2: there exists a real normed linear space and a subset of it that is
proximinal but not Chebyshev. -/
theorem exists_proximinal_not_chebyshev_subset :
    ∃ (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace ℝ X) (C : Set X),
      IsProximinalIn C ∧ ¬ IsChebyshev C := by
  refine ⟨ULift.{u} (ℝ × ℝ), inferInstance, inferInstance, horizontalSegment, ?_, ?_⟩
  · -- Every point is best-approximated by clamping its first coordinate to `[-1,1]`.
    intro x
    refine ⟨ULift.up (((clampToSegment x.down.1 : Set.Icc (-1 : ℝ) 1) : ℝ), 0), ?_⟩
    exact horizontal_segment_projection_is_best x
  · -- The point `(0,1)` has two distinct best approximations on the segment.
    intro hcheb
    let x0 : ULift.{u} (ℝ × ℝ) := ULift.up ((0 : ℝ), 1)
    let p0 : ULift.{u} (ℝ × ℝ) := ULift.up ((0 : ℝ), 0)
    let p1 : ULift.{u} (ℝ × ℝ) := ULift.up ((1 : ℝ), 0)
    obtain ⟨p, hp, hp_unique⟩ := hcheb x0
    have hp0_mem : p0 ∈ horizontalSegment := by
      constructor
      · rfl
      · constructor <;> norm_num
    have hp1_mem : p1 ∈ horizontalSegment := by
      constructor
      · rfl
      · constructor <;> norm_num
    have hp0_dist : dist x0 p0 = 1 := by
      norm_num [x0, p0, Prod.dist_eq, Real.dist_eq]
    have hp1_dist : dist x0 p1 = 1 := by
      norm_num [x0, p1, Prod.dist_eq, Real.dist_eq]
    have hp0_best : IsBestApproximation x0 horizontalSegment p0 := by
      constructor
      · exact hp0_mem
      · apply dist_eq_infDist_of_forall_le hp0_mem
        intro q hq
        rw [hp0_dist]
        exact one_le_dist_top_point_of_mem_horizontal_segment q hq
    have hp1_best : IsBestApproximation x0 horizontalSegment p1 := by
      constructor
      · exact hp1_mem
      · apply dist_eq_infDist_of_forall_le hp1_mem
        intro q hq
        rw [hp1_dist]
        exact one_le_dist_top_point_of_mem_horizontal_segment q hq
    have hp_eq_p0 : p = p0 := (hp_unique p0 hp0_best).symm
    have hp_eq_p1 : p = p1 := (hp_unique p1 hp1_best).symm
    have hp0_eq_hp1 : p0 = p1 := hp_eq_p0.symm.trans hp_eq_p1
    change ULift.up ((0 : ℝ), 0) = ULift.up ((1 : ℝ), 0) at hp0_eq_hp1
    norm_num at hp0_eq_hp1

/-! Source item: Chap03/Corollary_3_15 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
  [FiniteDimensional ℝ 𝓗]

-- Proof sketch: for the forward implication, use the defining best-approximation condition to show
-- that every point in the closure of `C` already belongs to `C`. For the reverse implication, fix
-- `x`, choose a minimizing sequence in the nonempty closed set `C`, use compactness of closed
-- bounded sets in finite dimensions to extract a convergent subsequence with limit in `C`, and
-- show that the limit realizes `Metric.infDist x C`.
/-- Corollary 3.15: in a finite-dimensional real Hilbert space, a nonempty set is proximal if and
only if it is closed. -/
theorem proximinal_iff_isClosed_of_nonempty {C : Set 𝓗} (hC : C.Nonempty) :
    IsProximinalIn C ↔ IsClosed C := by
  constructor
  · intro hprox
    rw [isProximinalIn_iff_forall_exists_bestApproximation] at hprox
    -- The governing invariant in the forward direction is `closure C ⊆ C`.
    refine (closure_subset_iff_isClosed).mp ?_
    intro x hx
    -- Realize the distance to `C` at the closure point `x`.
    obtain ⟨p, hpC, hpdist⟩ := hprox x
    -- A closure point has distance zero to `C`, so the realizing point must equal `x`.
    rw [Metric.infDist_zero_of_mem_closure hx] at hpdist
    have hxp : x = p := dist_eq_zero.mp hpdist
    simpa [hxp] using hpC
  · intro hclosed
    rw [isProximinalIn_iff_forall_exists_bestApproximation]
    intro x
    -- In finite dimensions, the proper-space attainment theorem realizes `infDist` on closed
    -- nonempty sets.
    obtain ⟨p, hpC, hpdist⟩ := hclosed.exists_infDist_eq_dist hC x
    exact ⟨p, hpC, hpdist.symm⟩

/-- Compatibility form of `proximinal_iff_isClosed_of_nonempty`. -/
theorem proximal_iff_isClosed_of_nonempty {C : Set 𝓗} (hC : C.Nonempty) :
    IsProximal C ↔ IsClosed C :=
  proximinal_iff_isClosed_of_nonempty hC

/-! Source item: Chap03/Theorem_3_16_1 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

omit [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗] in
/-- Helper for Theorem 3.16.1: a point of `C` whose norm distance realizes the subtype infimum is a
best approximation in the project API. -/
private theorem isBestApproximation_of_mem_and_norm_eq_iInf {C : Set 𝓗} {x p : 𝓗}
    (hpC : p ∈ C) (hpmin : ‖x - p‖ = ⨅ y : C, ‖x - y‖) : IsBestApproximation x C p := by
  constructor
  · exact hpC
  -- Rewrite the project distance to a set as the subtype infimum from mathlib's minimizer theorem.
  rw [Metric.infDist_eq_iInf]
  simpa [dist_eq_norm] using hpmin

/-- Helper for Theorem 3.16.1: the Hilbert-space projection theorem supplies at least one best
approximation in every nonempty closed convex set. -/
private theorem exists_isBestApproximation_of_nonempty_isClosed_convex {C : Set 𝓗}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ∀ x : 𝓗, ∃ p : 𝓗, IsBestApproximation x C p := by
  intro x
  -- Apply the complete-convex minimizer theorem and translate its conclusion to `IsBestApproximation`.
  rcases exists_norm_eq_iInf_of_complete_convex hC_nonempty hC_closed.isComplete hC_convex x with
    ⟨p, hpC, hpmin⟩
  refine ⟨p, ?_⟩
  exact isBestApproximation_of_mem_and_norm_eq_iInf hpC hpmin

omit [CompleteSpace 𝓗] in
/-- Helper for Theorem 3.16.1: convexity forces two best approximations to coincide. -/
private theorem eq_of_isBestApproximation_of_convex {C : Set 𝓗} (hC_convex : Convex ℝ C)
    {x p q : 𝓗}
    (hp : IsBestApproximation x C p) (hq : IsBestApproximation x C q) : p = q := by
  have hpmin : ‖x - p‖ = ⨅ y : C, ‖x - y‖ := by
    simpa [dist_eq_norm, Metric.infDist_eq_iInf] using hp.2
  have hqmin : ‖x - q‖ = ⨅ y : C, ‖x - y‖ := by
    simpa [dist_eq_norm, Metric.infDist_eq_iInf] using hq.2
  have hp_inner := (norm_eq_iInf_iff_real_inner_le_zero hC_convex hp.1).mp hpmin q hq.1
  have hq_inner := (norm_eq_iInf_iff_real_inner_le_zero hC_convex hq.1).mp hqmin p hp.1
  have hq_inner' : 0 ≤ ⟪x - q, q - p⟫_ℝ := by
    rw [show q - p = -(p - q) by abel, inner_neg_right]
    exact neg_nonneg.mpr hq_inner
  have hp_expand :
      ⟪x - p, q - p⟫_ℝ = ⟪x - q, q - p⟫_ℝ + ‖q - p‖ ^ 2 := by
    calc
      ⟪x - p, q - p⟫_ℝ = ⟪(x - q) + (q - p), q - p⟫_ℝ := by
        congr 1
        abel
      _ = ⟪x - q, q - p⟫_ℝ + ⟪q - p, q - p⟫_ℝ := by rw [inner_add_left]
      _ = ⟪x - q, q - p⟫_ℝ + ‖q - p‖ ^ 2 := by rw [real_inner_self_eq_norm_sq, sq]
  have hpq_sq : ‖q - p‖ ^ 2 ≤ 0 := by
    rw [hp_expand] at hp_inner
    nlinarith
  have hpq_eq : q - p = 0 := by
    apply norm_eq_zero.mp
    exact sq_eq_zero_iff.mp <| le_antisymm hpq_sq (sq_nonneg ‖q - p‖)
  exact (sub_eq_zero.mp hpq_eq).symm

-- Proof sketch: combine the Hilbert projection theorem for existence with the convex minimizer
-- characterization for uniqueness.
/-- Theorem 3.16.1: every nonempty closed convex subset of a real Hilbert space is a Chebyshev
set, equivalently each point has a unique nearest point in the set. -/
theorem isChebyshev_of_nonempty_isClosed_convex {C : Set 𝓗} (hC_nonempty : C.Nonempty)
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    IsChebyshev C := by
  intro x
  rcases exists_isBestApproximation_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex x with
    ⟨p, hp⟩
  refine ⟨p, hp, ?_⟩
  intro q hq
  exact (eq_of_isBestApproximation_of_convex hC_convex hp hq).symm

-- Proof sketch: specialize the Chebyshev conclusion of Theorem 3.16.1 at the given point.
/-- Every point in a real Hilbert space has a unique best approximation in a nonempty closed convex
set. -/
theorem existsUnique_bestApproximation_of_nonempty_isClosed_convex {C : Set 𝓗}
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ∀ x : 𝓗, ∃! p : 𝓗, IsBestApproximation x C p := by
  exact isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex

/-! Source item: Chap03/Example_3_10 -/
universe v


variable {I : Type v} [Fintype I] [DecidableEq I]
variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

omit [DecidableEq I] [CompleteSpace 𝓗] in
private lemma orthogonal_coordinate_sum_mem_span (e : I → 𝓗) (x : 𝓗) :
    (∑ i : I, ⟪x, e i⟫_ℝ • e i) ∈ Submodule.span ℝ (Set.range e) := by
  -- Each summand is a scalar multiple of a generator of the span.
  simpa using
    (Submodule.sum_mem (Submodule.span ℝ (Set.range e)) fun i _ ↦
      Submodule.smul_mem (Submodule.span ℝ (Set.range e)) _ <|
        Submodule.subset_span ⟨i, rfl⟩)

omit [DecidableEq I] [CompleteSpace 𝓗] in
private lemma orthonormal_span_error_sq_decomposition
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) (α : I → ℝ) :
    ‖x - ∑ i : I, α i • e i‖ ^ 2 =
      ‖x‖ ^ 2 - ∑ i : I, |⟪x, e i⟫_ℝ| ^ 2 + ∑ i : I, |α i - ⟪x, e i⟫_ℝ| ^ 2 := by
  -- Expand the squared norm and evaluate the mixed and quadratic terms in orthonormal
  -- coordinates.
  rw [norm_sub_sq_real]
  have h_inner : ⟪x, ∑ i : I, α i • e i⟫_ℝ = ∑ i : I, α i * ⟪x, e i⟫_ℝ := by
    simp [inner_sum, inner_smul_right]
  have h_norm : ‖∑ i : I, α i • e i‖ ^ 2 = ∑ i : I, |α i| ^ 2 := by
    calc
      ‖∑ i : I, α i • e i‖ ^ 2 = ⟪∑ i : I, α i • e i, ∑ i : I, α i • e i⟫_ℝ := by
        rw [real_inner_self_eq_norm_sq]
      _ = ∑ i : I, α i * α i := by
        simpa using he.inner_sum α α Finset.univ
      _ = ∑ i : I, |α i| ^ 2 := by
        simp [sq]
  rw [h_inner, h_norm]
  have h_expand :
      ∑ i : I, |α i - ⟪x, e i⟫_ℝ| ^ 2 =
        ∑ i : I, |α i| ^ 2 - 2 * ∑ i : I, α i * ⟪x, e i⟫_ℝ +
          ∑ i : I, |⟪x, e i⟫_ℝ| ^ 2 := by
    -- Complete the square pointwise and then sum the resulting identity.
    have h_pointwise :
        ∀ i : I,
          |α i - ⟪x, e i⟫_ℝ| ^ 2 =
            |α i| ^ 2 - (2 * (α i * ⟪x, e i⟫_ℝ)) + |⟪x, e i⟫_ℝ| ^ 2 := by
      intro i
      rw [sq_abs, sq_abs, sq_abs, sub_sq]
      ring
    calc
      ∑ i : I, |α i - ⟪x, e i⟫_ℝ| ^ 2 =
          ∑ i : I, (|α i| ^ 2 - (2 * (α i * ⟪x, e i⟫_ℝ)) + |⟪x, e i⟫_ℝ| ^ 2) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact h_pointwise i
      _ = ∑ i : I, |α i| ^ 2 - ∑ i : I, 2 * (α i * ⟪x, e i⟫_ℝ) +
            ∑ i : I, |⟪x, e i⟫_ℝ| ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = ∑ i : I, |α i| ^ 2 - 2 * ∑ i : I, α i * ⟪x, e i⟫_ℝ +
            ∑ i : I, |⟪x, e i⟫_ℝ| ^ 2 := by
        rw [← Finset.mul_sum]
  linarith

omit [DecidableEq I] [CompleteSpace 𝓗] in
private lemma orthonormal_span_error_sq_min_le
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) :
    ∀ β : I → ℝ,
      ‖x - ∑ i : I, ⟪x, e i⟫_ℝ • e i‖ ^ 2 ≤ ‖x - ∑ i : I, β i • e i‖ ^ 2 := by
  intro β
  -- The completed-square identity leaves only a sum of squares on the right-hand side.
  rw [orthonormal_span_error_sq_decomposition e he x (fun i ↦ ⟪x, e i⟫_ℝ),
    orthonormal_span_error_sq_decomposition e he x β]
  have hnonneg : 0 ≤ ∑ i : I, |β i - ⟪x, e i⟫_ℝ| ^ 2 := by
    exact Finset.sum_nonneg fun i hi ↦ sq_nonneg _
  simp at *
  linarith

omit [DecidableEq I] [CompleteSpace 𝓗] in
private lemma orthonormal_span_coefficients_eq_of_error_sq_eq_min
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) :
    ∀ β : I → ℝ,
      ‖x - ∑ i : I, β i • e i‖ ^ 2 = ‖x - ∑ i : I, ⟪x, e i⟫_ℝ • e i‖ ^ 2 →
        β = fun i ↦ ⟪x, e i⟫_ℝ := by
  intro β hβ
  -- Equality of the total errors forces the nonnegative sum of squares to vanish termwise.
  have hdecompβ := orthonormal_span_error_sq_decomposition e he x β
  have hdecomp0 := orthonormal_span_error_sq_decomposition e he x (fun i ↦ ⟪x, e i⟫_ℝ)
  rw [hβ] at hdecompβ
  rw [hdecomp0] at hdecompβ
  have hsum : ∑ i : I, |β i - ⟪x, e i⟫_ℝ| ^ 2 = 0 := by
    simpa using hdecompβ
  have hzero : ∀ i : I, |β i - ⟪x, e i⟫_ℝ| ^ 2 = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j hj ↦ sq_nonneg _)).1 hsum i (Finset.mem_univ i)
  funext i
  have hi : β i - ⟪x, e i⟫_ℝ = 0 := by
    apply abs_eq_zero.mp
    exact sq_eq_zero_iff.mp (hzero i)
  linarith

omit [DecidableEq I] [CompleteSpace 𝓗] in
private lemma finite_orthonormal_span_sum_inner_mem_span_and_sub_mem_orthogonal
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) :
    (∑ i : I, ⟪x, e i⟫_ℝ • e i) ∈ Submodule.span ℝ (Set.range e) ∧
      x - ∑ i : I, ⟪x, e i⟫_ℝ • e i ∈
        (Submodule.span ℝ (Set.range e) : Submodule ℝ 𝓗)ᗮ := by
  let V : Submodule ℝ 𝓗 := Submodule.span ℝ (Set.range e)
  let p0 : 𝓗 := ∑ i : I, ⟪x, e i⟫_ℝ • e i
  have hp0 : p0 ∈ V := by
    simpa [V, p0] using orthogonal_coordinate_sum_mem_span e x
  letI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range e)
  letI : CompleteSpace V := by infer_instance
  have hp0proj : V.starProjection x = p0 := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hp0
    intro y hy
    rcases (Submodule.mem_span_range_iff_exists_fun ℝ).mp hy with ⟨β, rfl⟩
    rw [inner_sub_left, inner_sum]
    simp [p0, inner_sum, inner_smul_right, he.inner_left_fintype]
  refine ⟨by simpa [V, p0] using hp0, ?_⟩
  simpa [V, p0, hp0proj] using V.sub_starProjection_mem_orthogonal x

omit [DecidableEq I] [CompleteSpace 𝓗] in
private lemma orthonormal_span_sum_inner_isBestApproximation
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) :
    IsBestApproximation x (((Submodule.span ℝ (Set.range e) : Submodule ℝ 𝓗) : Set 𝓗))
      (∑ i : I, ⟪x, e i⟫_ℝ • e i) := by
  let V : Submodule ℝ 𝓗 := Submodule.span ℝ (Set.range e)
  let p0 : 𝓗 := ∑ i : I, ⟪x, e i⟫_ℝ • e i
  have hmain := finite_orthonormal_span_sum_inner_mem_span_and_sub_mem_orthogonal e he x
  have hp0 : p0 ∈ V := by
    simpa [V, p0] using hmain.1
  letI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range e)
  letI : CompleteSpace V := by infer_instance
  have hp0_dist :
      dist x p0 = Metric.infDist x (V : Set 𝓗) := by
    have hp0proj : V.starProjection x = p0 := by
      apply Submodule.eq_starProjection_of_mem_orthogonal hp0
      simpa [V, p0] using hmain.2
    simpa [Metric.infDist_eq_iInf, dist_eq_norm, hp0proj] using V.starProjection_minimal x
  exact ⟨by simpa [V, p0] using hp0, by simpa [V] using hp0_dist⟩

-- Proof sketch: a finite-dimensional subspace of a Hilbert space is nonempty, closed, and convex,
-- so Theorem 3.16.1 applies directly.
omit [DecidableEq I] in
/-- The span of a finite family in a real Hilbert space is a Chebyshev set. -/
theorem finite_span_range_isChebyshev
    (e : I → 𝓗) :
    IsChebyshev (((Submodule.span ℝ (Set.range e) : Submodule ℝ 𝓗) : Set 𝓗)) := by
  let V : Submodule ℝ 𝓗 := Submodule.span ℝ (Set.range e)
  letI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range e)
  exact isChebyshev_of_nonempty_isClosed_convex
    ⟨0, by simp⟩
    (Submodule.closed_of_finiteDimensional V)
    V.convex

-- Proof sketch: identify the explicit orthogonal-coordinate sum as a best approximation and then
-- use uniqueness in the Chebyshev span.
omit [DecidableEq I] in
/-- Example 3.10: the projection onto the span of a finite orthonormal family is the orthogonal
coordinate sum. -/
theorem projectionPoint_finite_orthonormal_span_eq_sum_inner
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) :
    projectionPoint (((Submodule.span ℝ (Set.range e) : Submodule ℝ 𝓗) : Set 𝓗))
      (finite_span_range_isChebyshev e) x =
      ∑ i : I, ⟪x, e i⟫_ℝ • e i := by
  exact ((finite_span_range_isChebyshev e) x).unique
    (projectionPoint_isBestApproximation
      (((Submodule.span ℝ (Set.range e) : Submodule ℝ 𝓗) : Set 𝓗))
      (finite_span_range_isChebyshev e) x)
    (orthonormal_span_sum_inner_isBestApproximation e he x)

omit [DecidableEq I] [CompleteSpace 𝓗] in
/-- The orthogonal-coordinate sum `∑ i, ⟪x, e i⟫_ℝ • e i` is a best approximation to `x` from the
span of a finite orthonormal family. -/
theorem finite_orthonormal_span_sum_inner_isBestApproximation
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) :
    IsBestApproximation x (((Submodule.span ℝ (Set.range e) : Submodule ℝ 𝓗) : Set 𝓗))
      (∑ i : I, ⟪x, e i⟫_ℝ • e i) := by
  exact orthonormal_span_sum_inner_isBestApproximation e he x

-- Proof sketch: combine the best-approximation equality for the orthogonal-coordinate sum with the
-- Pythagorean identity for `x` decomposed into that sum and its orthogonal remainder.
omit [DecidableEq I] [CompleteSpace 𝓗] in
/-- The distance from `x` to the span of a finite orthonormal family is the square root of the
Pythagorean remainder. -/
theorem finite_orthonormal_span_infDist_eq_sqrt_sub_sum_inner_sq
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) :
    Metric.infDist x (((Submodule.span ℝ (Set.range e) : Submodule ℝ 𝓗) : Set 𝓗)) =
      Real.sqrt (‖x‖ ^ 2 - ∑ i : I, |⟪x, e i⟫_ℝ| ^ 2) := by
  let V : Set 𝓗 := (((Submodule.span ℝ (Set.range e) : Submodule ℝ 𝓗) : Set 𝓗))
  let p0 : 𝓗 := ∑ i : I, ⟪x, e i⟫_ℝ • e i
  have hp0dist : dist x p0 = Metric.infDist x V := by
    simpa [V, p0] using (finite_orthonormal_span_sum_inner_isBestApproximation e he x).2
  -- Specializing the decomposition to the orthogonal coordinates removes the final error term.
  have hsq : dist x p0 ^ 2 = ‖x‖ ^ 2 - ∑ i : I, |⟪x, e i⟫_ℝ| ^ 2 := by
    have hbase := orthonormal_span_error_sq_decomposition e he x (fun i ↦ ⟪x, e i⟫_ℝ)
    simpa [p0, dist_eq_norm] using hbase
  have hinf_sq : Metric.infDist x V ^ 2 = ‖x‖ ^ 2 - ∑ i : I, |⟪x, e i⟫_ℝ| ^ 2 := by
    rw [← hp0dist]
    exact hsq
  have hinf_nonneg : 0 ≤ Metric.infDist x V := Metric.infDist_nonneg
  calc
    Metric.infDist x V = Real.sqrt ((Metric.infDist x V) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hinf_nonneg]
    _ = Real.sqrt (‖x‖ ^ 2 - ∑ i : I, |⟪x, e i⟫_ℝ| ^ 2) := by
      rw [hinf_sq]

-- Proof sketch: expand `‖x - ∑ i, α i • e i‖ ^ 2` using the real inner product, evaluate the
-- mixed terms by orthonormality with `Orthonormal.inner_right_fintype`, and collect the resulting
-- squares to obtain the stated identity.
omit [DecidableEq I] [CompleteSpace 𝓗] in
/-- The squared norm of the error from an arbitrary linear combination splits into the orthogonal
projection remainder and the coefficient error term. -/
theorem finite_orthonormal_span_norm_sub_sum_smul_sq
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) (α : I → ℝ) :
    ‖x - ∑ i : I, α i • e i‖ ^ 2 =
      ‖x‖ ^ 2 - ∑ i : I, |⟪x, e i⟫_ℝ| ^ 2 + ∑ i : I, |α i - ⟪x, e i⟫_ℝ| ^ 2 := by
  -- This is exactly the completed-square helper established above.
  exact orthonormal_span_error_sq_decomposition e he x α

-- Proof sketch: apply `finite_orthonormal_span_norm_sub_sum_smul_sq` to `β`; the last summand is
-- a sum of squares and is therefore nonnegative, so the value at the coefficient family
-- `i ↦ ⟪x, e i⟫_ℝ` is minimal.
omit [DecidableEq I] [CompleteSpace 𝓗] in
/-- The orthogonal-coordinate family minimizes the squared distance to the span. -/
theorem finite_orthonormal_span_sum_inner_smul_sq_le
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) :
    ∀ β : I → ℝ,
      ‖x - ∑ i : I, ⟪x, e i⟫_ℝ • e i‖ ^ 2 ≤ ‖x - ∑ i : I, β i • e i‖ ^ 2 := by
  -- The coefficient error is a nonnegative sum of squares.
  exact orthonormal_span_error_sq_min_le e he x

-- Proof sketch: use `finite_orthonormal_span_norm_sub_sum_smul_sq` for `β`; if the squared error
-- attains the minimum value, the final sum of squares must vanish, hence every coordinate satisfies
-- `β i = ⟪x, e i⟫_ℝ`.
omit [DecidableEq I] [CompleteSpace 𝓗] in
/-- Equality of the minimal squared error forces the coefficient family to be the orthogonal
coordinates of `x`. -/
theorem finite_orthonormal_span_eq_inner_of_sq_eq_minimum
    (e : I → 𝓗) (he : Orthonormal ℝ e) (x : 𝓗) :
    ∀ β : I → ℝ,
      ‖x - ∑ i : I, β i • e i‖ ^ 2 = ‖x - ∑ i : I, ⟪x, e i⟫_ℝ • e i‖ ^ 2 →
        β = fun i ↦ ⟪x, e i⟫_ℝ := by
  -- Equality in the minimizing identity determines every coefficient.
  exact orthonormal_span_coefficients_eq_of_error_sq_eq_min e he x

/-! Source item: Chap03/Theorem_3_16_2 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

omit [CompleteSpace 𝓗] in
-- Proof sketch: rewrite `IsBestApproximation` as the metric equality defining a nearest point, then
-- `Mathlib.Analysis.InnerProductSpace.Projection.Minimal.norm_eq_iInf_iff_real_inner_le_zero`,
-- rewriting `Metric.infDist` as the corresponding `iInf`.
/-- In a convex subset of a real inner product space, a point is a best approximation to `x`
exactly when it lies in the set and satisfies the variational inequality against every point of the
set. -/
theorem isBestApproximation_iff_mem_and_inner_sub_right_nonpos {C : Set 𝓗}
    (hC_convex : Convex ℝ C) {x p : 𝓗} :
    IsBestApproximation x C p ↔ p ∈ C ∧ ∀ y ∈ C, ⟪y - p, x - p⟫_ℝ ≤ 0 := by
  rw [isBestApproximation_iff_mem_and_dist_eq_infDist]
  constructor
  · intro hp
    rw [dist_eq_norm, Metric.infDist_eq_iInf] at hp
    simp_rw [dist_eq_norm] at hp
    have hinner := (norm_eq_iInf_iff_real_inner_le_zero hC_convex hp.1).mp hp.2
    refine ⟨hp.1, ?_⟩
    intro y hy
    simpa [real_inner_comm] using hinner y hy
  · intro hp
    refine ⟨hp.1, ?_⟩
    rw [dist_eq_norm, Metric.infDist_eq_iInf]
    simp_rw [dist_eq_norm]
    refine (norm_eq_iInf_iff_real_inner_le_zero hC_convex hp.1).mpr ?_
    intro y hy
    simpa [real_inner_comm] using hp.2 y hy

omit [CompleteSpace 𝓗] in
-- Proof sketch: combine `projectionPoint_isBestApproximation` with the best-approximation
-- characterization above, and conversely use uniqueness in the Chebyshev hypothesis.
/-- In a convex Chebyshev set, a point is the projection of `x` exactly when it lies in the set and
satisfies the variational inequality against every point of the set. -/
theorem eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos {C : Set 𝓗} (hC : IsChebyshev C)
    (hC_convex : Convex ℝ C) {x p : 𝓗} :
    p = projectionPoint C hC x ↔ p ∈ C ∧ ∀ y ∈ C, ⟪y - p, x - p⟫_ℝ ≤ 0 := by
  constructor
  · intro hp
    exact
      (isBestApproximation_iff_mem_and_inner_sub_right_nonpos hC_convex).mp <|
        by simpa [hp] using projectionPoint_isBestApproximation C hC x
  · intro hp
    exact
      eq_projectionPoint_of_isBestApproximation C hC <|
        (isBestApproximation_iff_mem_and_inner_sub_right_nonpos hC_convex).mpr hp

-- Proof sketch: instantiate `eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos` with the
-- Chebyshev property supplied by `isChebyshev_of_nonempty_isClosed_convex`.
/-- Theorem 3.16.2: for a nonempty closed convex subset of a real Hilbert space, a point `p` is
the projection of `x` onto `C` exactly when `p ∈ C` and `⟪y - p, x - p⟫_ℝ ≤ 0` for every `y ∈ C`.
Here the projection is the canonical point
`projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x`,
which also realizes `Metric.infDist x C`. -/
theorem eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
    {C : Set 𝓗} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {x p : 𝓗} :
    p =
        projectionPoint C
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x ↔
      p ∈ C ∧ ∀ y ∈ C, ⟪y - p, x - p⟫_ℝ ≤ 0 := by
  -- The existence/uniqueness part is exactly Theorem 3.16.1, so the characterization reduces to
  -- the Chebyshev-convex case above.
  exact eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos
    (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) hC_convex

/-! Source item: Chap03/Proposition_3_19 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

-- Proof sketch: let `p := projectionPoint C _ (x - y)` and `q := y + p`. Then `q ∈ y +ᵥ C`.
-- Use the Hilbert-space characterization of projections onto nonempty closed convex sets on `C`
-- and transport the variational inequality by translation to show that `q` is the projection of
-- `x` onto `y +ᵥ C`.
/-- Proposition 3.19: the metric projection onto the translate `y + C = {y + z | z ∈ C}` is the
translate of the metric projection onto `C`, namely
`P_{y+C}(x) = y + P_C(x - y)`. -/
theorem projectionPoint_vadd_set_eq_add_projectionPoint {C : Set 𝓗}
    (x y : 𝓗) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    projectionPoint (y +ᵥ C)
        (isChebyshev_of_nonempty_isClosed_convex
          (hC_nonempty.vadd_set)
          (by simpa [vadd_eq_add] using hC_closed.left_addCoset y)
          (hC_convex.vadd y))
        x =
      y + projectionPoint C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) (x - y) := by
  let hC_cheb := isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex
  let hT_cheb : IsChebyshev (y +ᵥ C) :=
    isChebyshev_of_nonempty_isClosed_convex
      (hC_nonempty.vadd_set)
      (by simpa [vadd_eq_add] using hC_closed.left_addCoset y)
      (hC_convex.vadd y)
  let p := projectionPoint C hC_cheb (x - y)
  let q := y + p
  have hp_char :
      p ∈ C ∧ ∀ z ∈ C, ⟪z - p, (x - y) - p⟫_ℝ ≤ 0 := by
    -- Theorem 3.16.2 gives the variational characterization of `p = P_C (x - y)`.
    exact
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex).mp rfl
  have hq_proj :
      q =
        projectionPoint (y +ᵥ C) hT_cheb x := by
    -- Prove that the translated candidate `q` satisfies the translated variational inequality.
    refine
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        (hC_nonempty.vadd_set)
        (by simpa [vadd_eq_add] using hC_closed.left_addCoset y)
        (hC_convex.vadd y)).mpr ?_
    refine ⟨?_, ?_⟩
    · -- Membership is preserved by translation.
      change ∃ u ∈ C, y + u = q
      exact ⟨p, hp_char.1, by simp [q]⟩
    · intro w hw
      rcases (by simpa [Set.mem_vadd_set, vadd_eq_add] using hw : ∃ z ∈ C, y + z = w) with
        ⟨z, hz, rfl⟩
      -- The translated inner product is exactly the original one after substituting `w = y + z`.
      have hsub1 : (y + z) - (y + p) = z - p := by
        abel_nf
      have hsub2 : x - (y + p) = (x - y) - p := by
        abel_nf
      simpa [q, hsub1, hsub2] using hp_char.2 z hz
  -- The translated characterization identifies the canonical projection uniquely.
  simpa [q, p] using hq_proj.symm

/-! Source item: Chap03/Proposition_3_20 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

private noncomputable def projectionSequence
    (C : ℕ → Set 𝓗) (h_nonempty : ∀ n, (C n).Nonempty) (h_closed : ∀ n, IsClosed (C n))
    (h_convex : ∀ n, Convex ℝ (C n)) : ℕ → 𝓗 :=
  fun n ↦
    projectionPoint (C n)
      (isChebyshev_of_nonempty_isClosed_convex (h_nonempty n) (h_closed n) (h_convex n)) 0

private noncomputable def projectionEnergy
    (C : ℕ → Set 𝓗) (h_nonempty : ∀ n, (C n).Nonempty) (h_closed : ∀ n, IsClosed (C n))
    (h_convex : ∀ n, Convex ℝ (C n)) : ℕ → ℝ :=
  fun n ↦ ‖projectionSequence C h_nonempty h_closed h_convex n‖ ^ 2

/-- A projection onto a later set lies in every earlier set of an antitone family. -/
private lemma projection_mem_of_le
    (C : ℕ → Set 𝓗) (h_nonempty : ∀ n, (C n).Nonempty) (h_closed : ∀ n, IsClosed (C n))
    (h_convex : ∀ n, Convex ℝ (C n)) (h_anti : Antitone C) {m n : ℕ} (hmn : m ≤ n) :
    projectionSequence C h_nonempty h_closed h_convex n ∈ C m := by
  -- Then the canonical projection point onto `C n` belongs to every earlier set `C m`.
  exact h_anti hmn <|
    projectionPoint_mem (C n)
      (isChebyshev_of_nonempty_isClosed_convex (h_nonempty n) (h_closed n) (h_convex n)) 0

/-- The squared norms of the projection sequence are monotone. -/
private lemma projection_norm_sq_monotone
    (C : ℕ → Set 𝓗) (h_nonempty : ∀ n, (C n).Nonempty) (h_closed : ∀ n, IsClosed (C n))
    (h_convex : ∀ n, Convex ℝ (C n)) (h_anti : Antitone C) :
    Monotone (projectionEnergy C h_nonempty h_closed h_convex) := by
  intro m n hmn
  -- The later projection is an admissible competitor for the earlier projection problem.
  have hnorm :
      dist (0 : 𝓗) (projectionSequence C h_nonempty h_closed h_convex m) ≤
        dist (0 : 𝓗) (projectionSequence C h_nonempty h_closed h_convex n) := by
    calc
      dist (0 : 𝓗) (projectionSequence C h_nonempty h_closed h_convex m) =
          Metric.infDist 0 (C m) := by
            simpa [projectionSequence] using
              (projectionPoint_isBestApproximation (C m)
                (isChebyshev_of_nonempty_isClosed_convex
                  (h_nonempty m) (h_closed m) (h_convex m)) 0).2
      _ ≤ dist (0 : 𝓗) (projectionSequence C h_nonempty h_closed h_convex n) :=
        Metric.infDist_le_dist_of_mem <|
          projection_mem_of_le C h_nonempty h_closed h_convex h_anti hmn
  -- Squaring preserves the order because both norms are nonnegative.
  dsimp [projectionEnergy]
  have hnorm' : ‖projectionSequence C h_nonempty h_closed h_convex m‖ ≤
      ‖projectionSequence C h_nonempty h_closed h_convex n‖ := by
    simpa [projectionSequence, dist_eq_norm] using hnorm
  nlinarith [hnorm', norm_nonneg (projectionSequence C h_nonempty h_closed h_convex m),
    norm_nonneg (projectionSequence C h_nonempty h_closed h_convex n)]

/-- The projection gap is controlled by the increase in the energy. -/
private lemma projection_gap_sq_le_of_le
    (C : ℕ → Set 𝓗) (h_nonempty : ∀ n, (C n).Nonempty) (h_closed : ∀ n, IsClosed (C n))
    (h_convex : ∀ n, Convex ℝ (C n)) (h_anti : Antitone C) {m n : ℕ} (hmn : m ≤ n) :
    ‖projectionSequence C h_nonempty h_closed h_convex n -
        projectionSequence C h_nonempty h_closed h_convex m‖ ^ 2 ≤
      projectionEnergy C h_nonempty h_closed h_convex n -
        projectionEnergy C h_nonempty h_closed h_convex m := by
  let pm := projectionSequence C h_nonempty h_closed h_convex m
  let pn := projectionSequence C h_nonempty h_closed h_convex n
  have hpn_mem : pn ∈ C m := by
    -- Nestedness places the later projection point inside the earlier set.
    simpa [pn] using projection_mem_of_le C h_nonempty h_closed h_convex h_anti hmn
  have hproj :
      pm =
        projectionPoint (C m)
          (isChebyshev_of_nonempty_isClosed_convex (h_nonempty m) (h_closed m) (h_convex m)) 0 :=
    rfl
  have hinner_nonneg : 0 ≤ ⟪pn - pm, pm⟫_ℝ := by
    -- The variational inequality for the projection of `0` gives the sign of the cross term.
    have hchar :
        pm =
            projectionPoint (C m)
              (isChebyshev_of_nonempty_isClosed_convex
                (h_nonempty m) (h_closed m) (h_convex m)) 0 ↔
          pm ∈ C m ∧ ∀ y ∈ C m, ⟪y - pm, (0 : 𝓗) - pm⟫_ℝ ≤ 0 :=
      eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        (h_nonempty m) (h_closed m) (h_convex m)
    have hineq : ⟪pn - pm, (0 : 𝓗) - pm⟫_ℝ ≤ 0 := (hchar.mp hproj).2 pn hpn_mem
    simpa using neg_nonneg.mpr hineq
  have hsq := norm_add_sq_real (pn - pm) pm
  have hrewrite : (pn - pm) + pm = pn := by
    simp [pn, pm]
  -- Expand `‖pn‖²` and discard the nonnegative cross term.
  rw [hrewrite] at hsq
  dsimp [projectionEnergy]
  nlinarith

/-- The projection sequence onto the nested sets is Cauchy. -/
private lemma projection_sequence_cauchy
    (C : ℕ → Set 𝓗) (h_nonempty : ∀ n, (C n).Nonempty) (h_bounded : ∀ n, Bornology.IsBounded (C n))
    (h_closed : ∀ n, IsClosed (C n)) (h_convex : ∀ n, Convex ℝ (C n))
    (h_anti : Antitone C) :
    CauchySeq (projectionSequence C h_nonempty h_closed h_convex) := by
  let p := projectionSequence C h_nonempty h_closed h_convex
  let s := projectionEnergy C h_nonempty h_closed h_convex
  have hs_mono : Monotone s := projection_norm_sq_monotone C h_nonempty h_closed h_convex h_anti
  obtain ⟨R, hR_pos, hR⟩ := (h_bounded 0).exists_pos_norm_le
  have hp_mem_zero : ∀ n, p n ∈ C 0 := by
    intro n
    -- Every projection lies in the first set because the family is decreasing.
    simpa [p] using projection_mem_of_le C h_nonempty h_closed h_convex h_anti (Nat.zero_le n)
  have hs_bdd : BddAbove (Set.range s) := by
    refine ⟨R ^ 2, ?_⟩
    rintro _ ⟨n, rfl⟩
    -- Boundedness of `C 0` bounds every term of the energy sequence.
    have hpn_norm : ‖p n‖ ≤ R := hR (p n) (hp_mem_zero n)
    dsimp [s, projectionEnergy]
    nlinarith [hR_pos, hpn_norm, norm_nonneg (p n)]
  let L : ℝ := ⨆ n, s n
  have hs_lim : Filter.Tendsto s Filter.atTop (nhds L) := by
    -- A monotone bounded real sequence converges to its supremum.
    simpa [L] using tendsto_atTop_ciSup hs_mono hs_bdd
  have hsqrt_lim : Filter.Tendsto (fun N ↦ Real.sqrt (L - s N)) Filter.atTop (nhds 0) := by
    -- The tail energy above level `N` shrinks to zero, so its square root also tends to zero.
    have hsub_lim : Filter.Tendsto (fun N ↦ L - s N) Filter.atTop (nhds (L - L)) := by
      exact tendsto_const_nhds.sub hs_lim
    have hsqrt' :
        Filter.Tendsto (fun N ↦ Real.sqrt (L - s N)) Filter.atTop (nhds (Real.sqrt (L - L))) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hsub_lim
    simpa using hsqrt'
  refine cauchySeq_of_le_tendsto_0 (fun N ↦ Real.sqrt (L - s N)) ?_ hsqrt_lim
  intro n m N hNn hNm
  by_cases hnm : n ≤ m
  · have hgap :
        ‖p m - p n‖ ^ 2 ≤ s m - s n := by
      simpa [p, s, norm_sub_rev] using
        projection_gap_sq_le_of_le C h_nonempty h_closed h_convex h_anti hnm
    have htail_nonneg : 0 ≤ L - s N := sub_nonneg.mpr (le_ciSup hs_bdd N)
    have htail_sq : ‖p m - p n‖ ^ 2 ≤ L - s N := by
      have hsNn : s N ≤ s n := hs_mono hNn
      have hsmL : s m ≤ L := le_ciSup hs_bdd m
      linarith
    -- Compare the norm with the square root of the tail energy.
    rw [dist_eq_norm, norm_sub_rev]
    nlinarith [htail_sq, Real.sq_sqrt htail_nonneg, norm_nonneg (p m - p n),
      Real.sqrt_nonneg (L - s N)]
  · have hmn : m ≤ n := le_of_not_ge hnm
    have hgap :
        ‖p n - p m‖ ^ 2 ≤ s n - s m := by
      simpa [p, s] using
        projection_gap_sq_le_of_le C h_nonempty h_closed h_convex h_anti hmn
    have htail_nonneg : 0 ≤ L - s N := sub_nonneg.mpr (le_ciSup hs_bdd N)
    have htail_sq : ‖p n - p m‖ ^ 2 ≤ L - s N := by
      have hsNm : s N ≤ s m := hs_mono hNm
      have hsnL : s n ≤ L := le_ciSup hs_bdd n
      linarith
    -- The symmetric estimate gives the same tail bound in the other index order.
    rw [dist_eq_norm]
    nlinarith [htail_sq, Real.sq_sqrt htail_nonneg, norm_nonneg (p n - p m),
      Real.sqrt_nonneg (L - s N)]

/-- Proposition 3.20: a decreasing sequence of nonempty bounded closed convex subsets of a real
Hilbert space has nonempty intersection. -/
theorem nonempty_iInter_of_nonempty_bounded_isClosed_convex
    (C : ℕ → Set 𝓗) (h_nonempty : ∀ n, (C n).Nonempty) (h_bounded : ∀ n, Bornology.IsBounded (C n))
    (h_closed : ∀ n, IsClosed (C n)) (h_convex : ∀ n, Convex ℝ (C n)) (h_anti : Antitone C) :
    (⋂ n, C n).Nonempty := by
  let p := projectionSequence C h_nonempty h_closed h_convex
  have hp_cauchy : CauchySeq p :=
    projection_sequence_cauchy C h_nonempty h_bounded h_closed h_convex h_anti
  rcases cauchySeq_tendsto_of_complete hp_cauchy with ⟨q, hq_lim⟩
  refine ⟨q, ?_⟩
  simpa [Set.mem_iInter] using fun n ↦ by
    have htail_lim : Filter.Tendsto (fun k ↦ p (k + n)) Filter.atTop (nhds q) := by
    -- Shifting a convergent sequence preserves its limit.
      exact (Filter.tendsto_add_atTop_iff_nat n).2 hq_lim
    have htail_mem : ∀ k, p (k + n) ∈ C n := by
      intro k
      -- Every term of the shifted tail already lies in `C n`.
      simpa [p, Nat.add_comm] using projection_mem_of_le C h_nonempty h_closed h_convex h_anti
        (Nat.le_add_left n k)
    -- Closedness of each `C n` keeps the limit point inside that set.
    exact (h_closed n).mem_of_tendsto htail_lim (Filter.Eventually.of_forall htail_mem)

/-! Source item: Chap03/Proposition_3_21 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

section

variable {C : Set 𝓗}

-- Proof sketch: let `p := projectionPoint C hC x`. To show that the projection of
-- `p + t • (x - p)` is still `p`, it is enough to verify that `p` is again a best approximation
-- for the new point. Use the variational characterization of nearest points on convex Chebyshev
-- sets: the defining inequality for `p = projectionPoint C hC x` scales by the nonnegative factor
-- `t`, so `p` also satisfies the characterization at `p + t • (x - p)`.
/-- For a convex Chebyshev set, the projection of every point on the ray starting at
`projectionPoint C hC x` and pointing toward `x` remains `projectionPoint C hC x`. -/
theorem projectionPoint_ray_fixed (C : Set 𝓗) (hC : IsChebyshev C) (hC_convex : Convex ℝ C)
    (x : 𝓗) {t : ℝ} (ht : 0 ≤ t) :
    projectionPoint C hC (projectionPoint C hC x + t • (x - projectionPoint C hC x)) =
      projectionPoint C hC x := by
  -- Read off the projection variational inequality at the original point `x`.
  have hx :
      projectionPoint C hC x ∈ C ∧
        ∀ y ∈ C, ⟪y - projectionPoint C hC x, x - projectionPoint C hC x⟫_ℝ ≤ 0 := by
    exact
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos hC hC_convex).mp rfl
  -- Apply the same characterization at the point on the residual ray.
  have hray :
      projectionPoint C hC x =
        projectionPoint C hC (projectionPoint C hC x + t • (x - projectionPoint C hC x)) := by
    refine
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos hC hC_convex).mpr ?_
    refine ⟨hx.1, ?_⟩
    intro y hy
    -- The new displacement from `P x` is a nonnegative multiple of `x - P x`.
    calc
      ⟪y - projectionPoint C hC x,
          (projectionPoint C hC x + t • (x - projectionPoint C hC x)) -
            projectionPoint C hC x⟫_ℝ
          = ⟪y - projectionPoint C hC x, t • (x - projectionPoint C hC x)⟫_ℝ := by
              abel_nf
      _ = t * ⟪y - projectionPoint C hC x, x - projectionPoint C hC x⟫_ℝ := by
            rw [inner_smul_right]
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht (hx.2 y hy)
  simpa using hray.symm

/-- Proposition 3.21: if `C` is a nonempty closed convex subset of a real Hilbert space, then the
projection of every point on the ray starting at `P_C x` and pointing toward `x` remains `P_C x`.
-/
theorem projectionPoint_ray_fixed_of_nonempty_isClosed_convex
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (x : 𝓗)
    {t : ℝ} (ht : 0 ≤ t) :
    projectionPoint C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
        (projectionPoint C
            (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x +
          t •
            (x -
              projectionPoint C
                (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x)) =
      projectionPoint C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x := by
  simpa using
    projectionPoint_ray_fixed C
      (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
      hC_convex x ht

end

/-! Source item: Chap03/Corollary_3_22 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

section

variable {C : AffineSubspace ℝ 𝓗}
variable (hC_nonempty : (C : Set 𝓗).Nonempty) (hC_closed : IsClosed (C : Set 𝓗))

local notation "P" =>
  projectionPoint (C : Set 𝓗)
    (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex)

omit [CompleteSpace 𝓗] in
/-- Helper for Corollary 3.22: for a point `p ∈ C`, orthogonality of `x - p` to the direction
space is equivalent to orthogonality to every difference `y - z` with `y, z ∈ C`. -/
private lemma sub_mem_direction_orthogonal_iff {x p : 𝓗} (hp : p ∈ (C : Set 𝓗)) :
    x - p ∈ C.directionᗮ ↔
      ∀ y ∈ (C : Set 𝓗), ∀ z ∈ (C : Set 𝓗), ⟪y - z, x - p⟫_ℝ = 0 := by
  constructor
  · intro hx y hy z hz
    exact Submodule.inner_right_of_mem_orthogonal
      (by simpa [vsub_eq_sub] using C.vsub_mem_direction hy hz)
      hx
  · intro hx
    exact (C.direction.mem_orthogonal (x - p)).2 fun v hv ↦ by
      rcases (C.mem_direction_iff_eq_vsub_right hp v).mp hv with ⟨y, hy, rfl⟩
      simpa [vsub_eq_sub] using hx y hy p hp

/-- Helper for Corollary 3.22: on a nonempty closed affine subspace, the Chebyshev projection
coincides with the canonical affine orthogonal projection from mathlib. -/
theorem projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
    [Nonempty C] [C.direction.HasOrthogonalProjection] (x : 𝓗) :
    P x = (orthogonalProjection C x : 𝓗) := by
  have hCheb : IsChebyshev (C : Set 𝓗) :=
    isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex
  have hproj_best : IsBestApproximation x (C : Set 𝓗) (P x) := by
    simpa using projectionPoint_isBestApproximation (C : Set 𝓗) hCheb x
  have horth_best :
      IsBestApproximation x (C : Set 𝓗) (orthogonalProjection C x : 𝓗) := by
    refine ⟨by
      change ((orthogonalProjection C x : C) : 𝓗) ∈ C
      exact orthogonalProjection_mem x, ?_⟩
    simpa using dist_orthogonalProjection_eq_infDist C x
  exact ExistsUnique.unique (hCheb x) hproj_best horth_best

-- Proof sketch: identify the metric projector with `orthogonalProjection C`, use the canonical
-- characterization `q = orthogonalProjection C x ↔ q ∈ C ∧ x - q ∈ C.directionᗮ`, and rewrite
-- membership in `C.directionᗮ` as orthogonality to all differences `y - z` with `y, z ∈ C`.
/-- Corollary 3.22 (1): for a nonempty closed affine subspace of a real Hilbert space, a point is
the metric projection of `x` exactly when it lies in the affine subspace and the residual `x - p`
is orthogonal to every direction `y - z` with `y, z ∈ C`. -/
theorem eq_projectionPoint_iff_mem_and_inner_sub_eq_zero_of_nonempty_isClosed_affineSubspace
    {x p : 𝓗} :
    p = P x ↔
      p ∈ (C : Set 𝓗) ∧
        ∀ y ∈ (C : Set 𝓗), ∀ z ∈ (C : Set 𝓗), ⟪y - z, x - p⟫_ℝ = 0 := by
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  have hdir_closed : IsClosed (C.direction : Set 𝓗) :=
    (AffineSubspace.isClosed_direction_iff C).mpr hC_closed
  letI : IsClosed (C.direction : Set 𝓗) := hdir_closed
  letI : CompleteSpace C.direction := IsClosed.completeSpace_coe
  letI : C.direction.HasOrthogonalProjection := by
    infer_instance
  calc
    p = P x ↔ p = (orthogonalProjection C x : 𝓗) := by
      rw [projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
        hC_nonempty hC_closed]
    _ ↔ p ∈ (C : Set 𝓗) ∧ x - p ∈ C.directionᗮ := by
      simpa [eq_comm, vsub_eq_sub] using
        (coe_orthogonalProjection_eq_iff_mem :
          (orthogonalProjection C x : 𝓗) = p ↔ p ∈ (C : Set 𝓗) ∧ x - p ∈ C.directionᗮ)
    _ ↔ p ∈ (C : Set 𝓗) ∧
          ∀ y ∈ (C : Set 𝓗), ∀ z ∈ (C : Set 𝓗), ⟪y - z, x - p⟫_ℝ = 0 := by
      constructor
      · rintro ⟨hp, hx⟩
        exact ⟨hp, (sub_mem_direction_orthogonal_iff hp).mp hx⟩
      · rintro ⟨hp, hx⟩
        exact ⟨hp, (sub_mem_direction_orthogonal_iff hp).mpr hx⟩

-- Proof sketch: replace the metric projector by the canonical affine map
-- `orthogonalProjection C`, use that continuous affine maps commute with `AffineMap.lineMap`, and
-- translate back.
/-- Corollary 3.22 (2): the metric projection onto a nonempty closed affine subspace is an affine
operator. -/
theorem projectionPoint_lineMap_of_nonempty_isClosed_affineSubspace
    (x₁ x₂ : 𝓗) (t : ℝ) :
    P ((1 - t) • x₁ + t • x₂) = (1 - t) • P x₁ + t • P x₂ := by
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  have hdir_closed : IsClosed (C.direction : Set 𝓗) :=
    (AffineSubspace.isClosed_direction_iff C).mpr hC_closed
  letI : IsClosed (C.direction : Set 𝓗) := hdir_closed
  letI : CompleteSpace C.direction := IsClosed.completeSpace_coe
  letI : C.direction.HasOrthogonalProjection := by
    infer_instance
  calc
    P ((1 - t) • x₁ + t • x₂) = (orthogonalProjection C ((1 - t) • x₁ + t • x₂) : 𝓗) := by
      rw [projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
        hC_nonempty hC_closed]
    _ =
        ((AffineMap.lineMap
            (orthogonalProjection C x₁)
            (orthogonalProjection C x₂)
            t : C) : 𝓗) := by
      have hline :
          orthogonalProjection C ((1 - t) • x₁ + t • x₂) =
            AffineMap.lineMap (orthogonalProjection C x₁) (orthogonalProjection C x₂) t := by
        simpa [AffineMap.lineMap_apply_module] using
          (orthogonalProjection C).apply_lineMap x₁ x₂ t
      exact congrArg Subtype.val hline
    _ = AffineMap.lineMap (orthogonalProjection C x₁ : 𝓗) (orthogonalProjection C x₂ : 𝓗) t := by
      rfl
    _ = (1 - t) • (orthogonalProjection C x₁ : 𝓗) + t • (orthogonalProjection C x₂ : 𝓗) := by
      simp [AffineMap.lineMap_apply_module]
    _ = (1 - t) • P x₁ + t • P x₂ := by
      rw [projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
          hC_nonempty hC_closed,
        projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
          hC_nonempty hC_closed]

end

/-! Source item: Chap03/Example_3_23 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/- A hyperplane with nonzero normal is the translate of the kernel of
`x ↦ ⟪x, u⟫_ℝ`. -/
private lemma innerProductLevelSet_eq_mk'_ker_innerSLFlip (u : 𝓗) (η : ℝ) (hu : u ≠ 0) :
    innerProductLevelSet u η =
      (AffineSubspace.mk' ((η / ‖u‖ ^ 2) • u) ((innerSLFlip ℝ u).ker) : Set 𝓗) := by
  have hu_norm : ‖u‖ ≠ 0 := by
    simpa using hu
  have hu_sq : ‖u‖ ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_ne_zero hu_norm hu_norm
  ext x
  constructor
  · intro hx
    -- The hyperplane equation says that the displacement from the base point has zero inner
    -- product with `u`, so it lies in the kernel direction.
    change x ∈ AffineSubspace.mk' ((η / ‖u‖ ^ 2) • u) ((innerSLFlip ℝ u).ker)
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker]
    calc
      ((innerSLFlip ℝ u) (x - (η / ‖u‖ ^ 2) • u))
          = ⟪x - (η / ‖u‖ ^ 2) • u, u⟫_ℝ := by
              rw [innerSLFlip_apply_apply]
      _ = ⟪x, u⟫_ℝ - (η / ‖u‖ ^ 2) * ⟪u, u⟫_ℝ := by
            rw [inner_sub_left, real_inner_smul_left]
      _ = η - η := by
            rw [mem_innerProductLevelSet_iff.mp hx, real_inner_self_eq_norm_sq]
            field_simp [hu_sq]
      _ = 0 := by
            ring
  · intro hx
    -- Conversely, a kernel displacement means the point has the prescribed inner product with `u`.
    rw [mem_innerProductLevelSet_iff]
    change x ∈ AffineSubspace.mk' ((η / ‖u‖ ^ 2) • u) ((innerSLFlip ℝ u).ker) at hx
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker] at hx
    change ((innerSLFlip ℝ u) (x - (η / ‖u‖ ^ 2) • u)) = 0 at hx
    calc
      ⟪x, u⟫_ℝ
          = ((innerSLFlip ℝ u) (x - (η / ‖u‖ ^ 2) • u)) + (η / ‖u‖ ^ 2) * ⟪u, u⟫_ℝ := by
              rw [innerSLFlip_apply_apply, inner_sub_left, real_inner_smul_left]
              ring
      _ = η := by
            rw [hx, real_inner_self_eq_norm_sq]
            field_simp [hu_sq]
            ring

-- Proof sketch: write `hyperplane u η` as the preimage of the closed singleton `{η}` under the
-- continuous linear functional `x ↦ ⟪x, u⟫_ℝ`.
/-- The hyperplane cut out by a continuous real inner-product functional is closed. -/
theorem hyperplane_isClosed (u : 𝓗) (η : ℝ) :
    IsClosed (innerProductLevelSet u η) := by
  -- The defining equation is the preimage of the closed singleton `{η}` under `innerSLFlip`.
  have h_closed_preimage : IsClosed ((innerSLFlip ℝ u) ⁻¹' ({η} : Set ℝ)) :=
    isClosed_singleton.preimage (innerSLFlip ℝ u).continuous
  simpa [innerProductLevelSet, innerSLFlip_apply_apply] using
    h_closed_preimage

/- The normal correction sends `x` onto `innerProductLevelSet u η`. -/
private lemma corrected_point_mem_hyperplane (u : 𝓗) (η : ℝ) (hu : u ≠ 0) (x : 𝓗) :
    x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u ∈ innerProductLevelSet u η := by
  have hu_norm : ‖u‖ ≠ 0 := by
    simpa using hu
  have hu_sq : ‖u‖ ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_ne_zero hu_norm hu_norm
  -- Compute the inner product of the corrected point with the normal vector.
  rw [mem_innerProductLevelSet_iff]
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

/-- Helper for Example 3.23: the distance from `x` to its normal correction is the normalized
absolute inner-product defect. -/
private lemma dist_to_corrected_point_eq_abs_inner_sub_div_norm
    (u : 𝓗) (η : ℝ) (hu : u ≠ 0) (x : 𝓗) :
    dist x (x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u) = |⟪x, u⟫_ℝ - η| / ‖u‖ := by
  have hu_norm : ‖u‖ ≠ 0 := by
    simpa using hu
  -- Collapse the distance to the norm of the correction vector and simplify the scalar factor.
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

/-- Helper for Example 3.23: the orthogonal foot of `x` on `innerProductLevelSet u η` realizes the
distance to that hyperplane. -/
private lemma orthogonal_foot_isBestApproximation_hyperplane
    (u : 𝓗) (η : ℝ) (hu : u ≠ 0) (x : 𝓗) :
    IsBestApproximation x (innerProductLevelSet u η)
      (x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u) := by
  -- Match the explicit orthogonal foot with the defining best-approximation predicate.
  rw [isBestApproximation_iff_mem_and_dist_eq_infDist]
  refine ⟨corrected_point_mem_hyperplane u η hu x, ?_⟩
  rw [dist_to_corrected_point_eq_abs_inner_sub_div_norm u η hu x,
    infDist_hyperplane_eq_abs_inner_sub_div_norm x u η hu]

variable [CompleteSpace 𝓗]

-- Proof sketch: the hyperplane is nonempty by the explicit point `((η / ‖u‖ ^ 2) • u)`, it is
-- closed by `hyperplane_isClosed`, and it is convex because it is an affine subspace; then apply
-- the Hilbert-space nearest-point theorem for nonempty closed convex sets.
/-- A closed hyperplane in a real Hilbert space is a Chebyshev set. -/
theorem hyperplane_isChebyshev (u : 𝓗) (η : ℝ) (hu : u ≠ 0) :
    IsChebyshev (innerProductLevelSet u η) := by
  have h_nonempty : (innerProductLevelSet u η).Nonempty := by
    refine ⟨((η / ‖u‖ ^ 2) • u), ?_⟩
    rw [innerProductLevelSet_eq_mk'_ker_innerSLFlip u η hu]
    exact AffineSubspace.self_mem_mk' _ _
  have h_convex : Convex ℝ (innerProductLevelSet u η) := by
    rw [innerProductLevelSet_eq_mk'_ker_innerSLFlip u η hu]
    exact (AffineSubspace.mk' ((η / ‖u‖ ^ 2) • u) ((innerSLFlip ℝ u).ker)).convex
  -- The general Hilbert-space projection theorem applies once the hyperplane is seen to be
  -- nonempty, closed, and convex.
  exact isChebyshev_of_nonempty_isClosed_convex h_nonempty (hyperplane_isClosed u η) h_convex

-- Proof sketch: show that the displayed point lies in `hyperplane u η`, and then use uniqueness of
-- best approximations in the Chebyshev set `hyperplane u η` to identify it with the canonical
-- projection point.
/-- Example 3.23: the metric projection of `x` onto the hyperplane
`innerProductLevelSet u η = {z | ⟪z, u⟫_ℝ = η}` is obtained by correcting `x` along the normal
vector `u`. -/
theorem projectionPoint_hyperplane_eq_explicit (u : 𝓗) (η : ℝ) (hu : u ≠ 0) (x : 𝓗) :
    projectionPoint (innerProductLevelSet u η) (hyperplane_isChebyshev u η hu) x =
      x + ((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u := by
  let p := x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u
  have hp_best : IsBestApproximation x (innerProductLevelSet u η) p := by
    -- The source proof’s orthogonal-foot candidate already realizes the distance.
    simpa [p] using orthogonal_foot_isBestApproximation_hyperplane u η hu x
  have hp_proj :
      p = projectionPoint (innerProductLevelSet u η) (hyperplane_isChebyshev u η hu) x := by
    -- Chebyshev uniqueness identifies any best approximation with the canonical projection point.
    exact (hyperplane_isChebyshev u η hu x).unique hp_best
      (projectionPoint_isBestApproximation (innerProductLevelSet u η)
        (hyperplane_isChebyshev u η hu) x)
  have hscalar :
      -((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) = (η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2 := by
    ring
  have hsmul :
      (-((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2)) • u = ((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u := by
    exact congrArg (fun t : ℝ ↦ t • u) hscalar
  -- Rewrite the subtraction-form orthogonal foot into the textbook additive formula.
  calc
    projectionPoint (innerProductLevelSet u η) (hyperplane_isChebyshev u η hu) x = p := hp_proj.symm
    _ = x + ((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u := by
      calc
        p = x + (-((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2)) • u := by
              simp [p, sub_eq_add_neg]
        _ = x + ((η - ⟪x, u⟫_ℝ) / ‖u‖ ^ 2) • u := by
              rw [hsmul]

-- Proof sketch: use that the projection point is a best approximation, so its distance to `x`
-- equals `Metric.infDist x (innerProductLevelSet u η)`, and then apply the hyperplane distance
-- formula `infDist_hyperplane_eq_abs_inner_sub_div_norm`.
/-- The distance from `x` to its projection onto `innerProductLevelSet u η` is the normalized
absolute inner-product defect. -/
theorem dist_projectionPoint_hyperplane_eq_abs_inner_sub_div_norm
    (u : 𝓗) (η : ℝ) (hu : u ≠ 0) (x : 𝓗) :
    dist x (projectionPoint (innerProductLevelSet u η) (hyperplane_isChebyshev u η hu) x) =
      |⟪x, u⟫_ℝ - η| / ‖u‖ := by
  -- The canonical projection distance is exactly the set distance, and Chapter 2 already computed
  -- that set distance for hyperplanes.
  calc
    dist x (projectionPoint (innerProductLevelSet u η) (hyperplane_isChebyshev u η hu) x) =
        Metric.infDist x (innerProductLevelSet u η) :=
      (projectionPoint_isBestApproximation
        (innerProductLevelSet u η) (hyperplane_isChebyshev u η hu) x).2
    _ = |⟪x, u⟫_ℝ - η| / ‖u‖ :=
      infDist_hyperplane_eq_abs_inner_sub_div_norm x u η hu

/-! Source item: Chap03/Corollary_3_24 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

section

variable (V : ClosedSubmodule ℝ 𝓗) (x p : 𝓗)

-- Proof sketch: use the uniqueness characterization of orthogonal projection onto a complete
-- subspace. One direction combines `starProjection_apply_mem` with
-- `sub_starProjection_mem_orthogonal`; the converse uses
-- `eq_starProjection_of_mem_orthogonal`.
/-- Corollary 3.24 (1): textbook clause (i). A point is the orthogonal projection of `x` onto the
closed subspace `V` exactly when it lies in `V` and the residual vector lies in `Vᗮ`. -/
theorem starProjection_eq_iff_mem_and_sub_mem_orthogonal :
    V.starProjection x = p ↔ p ∈ V ∧ x - p ∈ Vᗮ := by
  -- The forward implication is exactly the packaged membership and orthogonality
  -- of `starProjection`.
  constructor
  · intro hp
    rw [← hp]
    exact
      ⟨(V : Submodule ℝ 𝓗).starProjection_apply_mem x,
        (V : Submodule ℝ 𝓗).sub_starProjection_mem_orthogonal x⟩
  · rintro ⟨hpV, horth⟩
    -- Uniqueness of orthogonal projection gives the converse direction.
    exact (V : Submodule ℝ 𝓗).eq_starProjection_of_mem_orthogonal hpV horth

-- Proof sketch: rewrite the left inner product using
-- `inner_orthogonalProjection_eq_of_mem_left` with the projected vector, then identify
-- `⟪P_V x, P_V x⟫` with `‖P_V x‖ ^ 2`.
/-- Corollary 3.24 (2): textbook clause (ii). The squared norm of the orthogonal projection equals
its inner product with the original vector. -/
theorem norm_sq_orthogonalProjection_eq_inner_starProjection :
    ‖V.orthogonalProjection x‖ ^ 2 = ⟪V.starProjection x, x⟫_ℝ := by
  -- Mathlib already identifies the real part of this inner product with the squared norm.
  simpa using ((V : Submodule ℝ 𝓗).re_inner_starProjection_eq_normSq x).symm

-- Proof sketch: the orthogonal projector is already a continuous linear map, and the standard
-- norm estimate `orthogonalProjection_norm_le` yields operator norm at most `1`.
/-- Corollary 3.24 (3): textbook clause (iii). The orthogonal projector onto `V` is bounded, with
operator norm at most `1`. -/
theorem norm_starProjection_le_one :
    ‖V.starProjection‖ ≤ 1 := by
  -- The orthogonal projector is a contraction.
  exact (V : Submodule ℝ 𝓗).starProjection_norm_le

-- Proof sketch: apply the standard operator-norm formula for orthogonal projection onto a
-- nontrivial subspace.
/-- Corollary 3.24 (4): textbook clause (iii). If `V` is nontrivial, then the orthogonal
projector onto `V` has operator norm `1`. -/
theorem norm_starProjection_eq_one_of_ne_bot (hV : V ≠ ⊥) :
    ‖V.starProjection‖ = 1 := by
  -- Translate nontriviality from closed submodules to ordinary submodules.
  have hV' : (V : Submodule ℝ 𝓗) ≠ ⊥ := by
    intro h
    exact hV (ClosedSubmodule.toSubmodule_injective h)
  -- Then apply the standard norm formula for orthogonal projection.
  exact (V : Submodule ℝ 𝓗).norm_starProjection hV'

-- Proof sketch: if `V = ⊥`, rewrite the projector as the zero projection and simplify its norm.
/-- Corollary 3.24 (5): textbook clause (iii). If `V = {0}`, then the orthogonal projector onto
`V` has operator norm `0`. -/
theorem norm_starProjection_eq_zero_of_eq_bot (hV : V = ⊥) :
    ‖V.starProjection‖ = 0 := by
  -- The projector onto the zero subspace is the zero map.
  rw [hV]
  simp

-- Proof sketch: use the closed-subspace identity `(Vᗮ)ᗮ = V`.
/-- Corollary 3.24 (6): textbook clause (iv). The double orthogonal complement of a closed subspace
is the subspace itself. -/
theorem orthogonal_orthogonal_eq :
    Vᗮᗮ = V := by
  -- Closed subspaces are equal to their double orthogonal complements.
  exact ClosedSubmodule.orthogonal_orthogonal_eq V

-- Proof sketch: apply the canonical decomposition of the identity into the projections onto `V`
-- and `Vᗮ`.
/-- Corollary 3.24 (7): textbook clause (v). The orthogonal projector onto `Vᗮ` is `Id - P_V`. -/
theorem starProjection_orthogonal_eq_one_sub :
    Vᗮ.starProjection = 1 - V.starProjection := by
  -- Mathlib packages the decomposition `Id = P_V + P_{Vᗮ}` as this projection identity.
  exact (V : Submodule ℝ 𝓗).starProjection_orthogonal'

-- Proof sketch: combine the symmetry of orthogonal projection with the standard equivalence
-- between symmetry and equality to the adjoint for continuous linear maps.
/-- Corollary 3.24 (8): textbook clause (vi). The orthogonal projector onto `V` is self-adjoint. -/
theorem adjoint_starProjection_eq :
    V.starProjection.adjoint = V.starProjection := by
  -- Orthogonal projections are self-adjoint operators.
  simpa using (isSelfAdjoint_starProjection (V : Submodule ℝ 𝓗)).adjoint_eq

-- Proof sketch: apply the Pythagorean identity coming from the decomposition
-- `x = P_V x + P_{Vᗮ} x`.
/-- Corollary 3.24 (9): textbook clause (vii). The norm of `x` splits as the sum of the squared
norms of its projections onto `V` and `Vᗮ`. -/
theorem norm_sq_eq_add_norm_sq_orthogonalProjection :
    ‖x‖ ^ 2 =
      ‖V.orthogonalProjection x‖ ^ 2 + ‖Vᗮ.orthogonalProjection x‖ ^ 2 := by
  -- This is the Pythagorean theorem for the orthogonal decomposition of `x`.
  exact Submodule.norm_sq_eq_add_norm_sq_projection x (V : Submodule ℝ 𝓗)

-- Helper for Corollary 3.24: the distance from `x` to `V` equals the norm of the residual
-- `x - P_V x`.
private theorem infDist_eq_norm_sub_starProjection :
    Metric.infDist x (V : Set 𝓗) = ‖x - V.starProjection x‖ := by
  -- Expand `infDist` into the infimum of distances to points of `V`.
  rw [Metric.infDist_eq_iInf]
  -- Rewrite those distances as ambient-space norms.
  simp_rw [dist_eq_norm]
  -- The residual of the orthogonal projection realizes the infimum.
  simpa using ((V : Submodule ℝ 𝓗).starProjection_minimal x).symm

-- Proof sketch: identify the distance from `x` to `V` with the norm of `x - P_V x`, then use the
-- formula `P_{Vᗮ} = Id - P_V`.
/-- Corollary 3.24 (10): textbook clause (vii). The distance from `x` to `V` is the norm of the
orthogonal component of `x` along `Vᗮ`. -/
theorem infDist_eq_norm_orthogonalProjection_orthogonal :
    Metric.infDist x (V : Set 𝓗) = ‖Vᗮ.orthogonalProjection x‖ := by
  -- First rewrite the distance as the norm of the orthogonal residual.
  rw [infDist_eq_norm_sub_starProjection]
  -- Then identify that residual with the projection onto `Vᗮ`.
  exact (congrArg norm ((V : Submodule ℝ 𝓗).orthogonalProjection_orthogonal x)).symm

-- Proof sketch: apply the previous distance formula to the closed subspace `Vᗮ`, then use
-- `(Vᗮ)ᗮ = V`.
/-- Corollary 3.24 (11): textbook clause (vii). The distance from `x` to `Vᗮ` is the norm of the
projection of `x` onto `V`. -/
theorem infDist_orthogonal_eq_norm_orthogonalProjection :
    Metric.infDist x (Vᗮ : Set 𝓗) = ‖V.orthogonalProjection x‖ := by
  -- Apply the distance formula to `Vᗮ`.
  rw [infDist_eq_norm_sub_starProjection]
  -- The residual to `Vᗮ` is exactly the projection onto `V`.
  simp

end

/-! Source item: Chap03/Proposition_3_25 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

private abbrev spanClosure (C : Set 𝓗) : Submodule ℝ 𝓗 :=
  (Submodule.span ℝ C).topologicalClosure

private abbrev spanClosureSubset (C : Set 𝓗) : Set (spanClosure C) :=
  (Subtype.val : spanClosure C → 𝓗) ⁻¹' C

/-- Helper for Proposition 3.25: every point of `C` lies in the closed linear span of `C`. -/
private lemma mem_spanClosure_of_mem {C : Set 𝓗} {z : 𝓗} (hz : z ∈ C) :
    z ∈ spanClosure C := by
  -- Points of `C` lie in `closure C`, and that closure sits inside the closed span.
  exact Submodule.closure_subset_topologicalClosure_span C (subset_closure hz)

section MetricHelpers

variable {X : Type u} [MetricSpace X]

/-- Helper for Proposition 3.25: a point realizes `Metric.infDist` exactly when it is no farther
than every other point of the set. -/
private lemma dist_eq_infDist_iff_forall_dist_le {S : Set X} {x p : X} (hp : p ∈ S) :
    dist x p = Metric.infDist x S ↔ ∀ z ∈ S, dist x p ≤ dist x z := by
  refine ⟨?_, ?_⟩
  · intro h z hz
    -- Rewriting by the realized infimum turns the claim into the standard lower bound.
    rw [h]
    exact Metric.infDist_le_dist_of_mem hz
  · intro h
    -- The minimizing inequalities give both bounds on `Metric.infDist`.
    refine le_antisymm ?_ (Metric.infDist_le_dist_of_mem hp)
    exact (Metric.le_infDist ⟨p, hp⟩).2 fun z hz ↦ h z hz

end MetricHelpers

section Complete

variable [CompleteSpace 𝓗]

/-- Helper for Proposition 3.25: for points in the closed span, the distance to `x` splits into
the distance to the orthogonal projection plus the fixed orthogonal residual. -/
private lemma dist_sq_eq_dist_sq_projection_add_residual_sq
    (C : Set 𝓗) {x z : 𝓗} (hz : z ∈ spanClosure C) :
    dist x z ^ 2 =
      dist ((spanClosure C).starProjection x) z ^ 2 +
        ‖x - (spanClosure C).starProjection x‖ ^ 2 := by
  have hpyth :=
    Submodule.norm_sq_eq_add_norm_sq_starProjection (x - z) (spanClosure C)
  have hz' : (spanClosure C).starProjection z = z := by
    -- Projecting a vector already in the subspace does nothing.
    exact Submodule.starProjection_mem_subspace_eq_self ⟨z, hz⟩
  have horth : (spanClosure C)ᗮ.starProjection z = 0 := by
    -- The orthogonal-complement projection vanishes on the subspace itself.
    exact Submodule.starProjection_orthogonal_apply_eq_zero hz
  have hres :
      (spanClosure C)ᗮ.starProjection x = x - (spanClosure C).starProjection x := by
    -- The orthogonal component is the residual after subtracting the projection.
    simpa using
      (show (spanClosure C)ᗮ.starProjection x = x - (spanClosure C).starProjection x from
        Submodule.starProjection_orthogonal_val x)
  calc
    dist x z ^ 2 = ‖x - z‖ ^ 2 := by
      rw [dist_eq_norm]
    _ = ‖(spanClosure C).starProjection (x - z)‖ ^ 2 +
          ‖(spanClosure C)ᗮ.starProjection (x - z)‖ ^ 2 := hpyth
    _ = ‖(spanClosure C).starProjection x - z‖ ^ 2 +
          ‖(spanClosure C)ᗮ.starProjection x -
            (spanClosure C)ᗮ.starProjection z‖ ^ 2 := by
      rw [ContinuousLinearMap.map_sub, ContinuousLinearMap.map_sub, hz']
    _ = ‖(spanClosure C)ᗮ.starProjection x - (spanClosure C)ᗮ.starProjection z‖ ^ 2 +
          ‖(spanClosure C).starProjection x - z‖ ^ 2 := by
      ring
    _ = ‖(spanClosure C)ᗮ.starProjection x‖ ^ 2 +
          ‖(spanClosure C).starProjection x - z‖ ^ 2 := by
      rw [horth, sub_zero]
    _ = ‖x - (spanClosure C).starProjection x‖ ^ 2 +
          dist ((spanClosure C).starProjection x) z ^ 2 := by
      rw [hres, dist_eq_norm]
    _ = dist ((spanClosure C).starProjection x) z ^ 2 +
          ‖x - (spanClosure C).starProjection x‖ ^ 2 := by
      ring

/-- Helper for Proposition 3.25: for points in the closed span, comparing their distances to `x`
is equivalent to comparing their distances to the projection of `x` onto the closed span. -/
private lemma projection_dist_le_iff
    (C : Set 𝓗) {x p z : 𝓗} (hp : p ∈ spanClosure C) (hz : z ∈ spanClosure C) :
    dist x p ≤ dist x z ↔
      dist ((spanClosure C).starProjection x) p ≤ dist ((spanClosure C).starProjection x) z := by
  have hpdecomp :
      dist x p ^ 2 =
        dist ((spanClosure C).starProjection x) p ^ 2 +
          ‖x - (spanClosure C).starProjection x‖ ^ 2 :=
    dist_sq_eq_dist_sq_projection_add_residual_sq C hp
  have hzdecomp :
      dist x z ^ 2 =
        dist ((spanClosure C).starProjection x) z ^ 2 +
          ‖x - (spanClosure C).starProjection x‖ ^ 2 :=
    dist_sq_eq_dist_sq_projection_add_residual_sq C hz
  have hxp_nonneg : 0 ≤ dist x p := dist_nonneg
  have hxz_nonneg : 0 ≤ dist x z := dist_nonneg
  have hpp_nonneg : 0 ≤ dist ((spanClosure C).starProjection x) p := dist_nonneg
  have hpz_nonneg : 0 ≤ dist ((spanClosure C).starProjection x) z := dist_nonneg
  constructor
  · intro h
    -- Squaring preserves the inequality because all distances are nonnegative.
    have hsquare : dist x p ^ 2 ≤ dist x z ^ 2 := by
      nlinarith
    have hprojSquare :
        dist ((spanClosure C).starProjection x) p ^ 2 ≤
          dist ((spanClosure C).starProjection x) z ^ 2 := by
      nlinarith [hpdecomp, hzdecomp, hsquare]
    nlinarith
  · intro h
    -- The same cancellation works in reverse because the residual term is identical.
    have hsquare :
        dist ((spanClosure C).starProjection x) p ^ 2 ≤
          dist ((spanClosure C).starProjection x) z ^ 2 := by
      nlinarith
    have hxSquare : dist x p ^ 2 ≤ dist x z ^ 2 := by
      nlinarith [hpdecomp, hzdecomp, hsquare]
    nlinarith

-- Helper for Proposition 3.25: realizing the distance to `C` in the ambient Hilbert space is
-- equivalent to realizing the distance to `C`, viewed inside its closed span.
omit [CompleteSpace 𝓗] in
private lemma dist_eq_infDist_spanClosureSubset_iff_ambient
    (C : Set 𝓗) {v p : spanClosure C} (hp : p ∈ spanClosureSubset C) :
    dist v p = Metric.infDist v (spanClosureSubset C) ↔
      dist (v : 𝓗) (p : 𝓗) = Metric.infDist (v : 𝓗) C := by
  constructor
  · intro h
    have hiff :
        dist v p = Metric.infDist v (spanClosureSubset C) ↔
          ∀ z ∈ spanClosureSubset C, dist v p ≤ dist v z :=
      dist_eq_infDist_iff_forall_dist_le hp
    have hmin : ∀ z ∈ spanClosureSubset C, dist v p ≤ dist v z :=
      hiff.mp h
    have hmin' : ∀ z ∈ C, dist (v : 𝓗) (p : 𝓗) ≤ dist (v : 𝓗) z := by
      -- Any ambient competitor in `C` becomes a subtype competitor in the closed span.
      intro z hz
      simpa [spanClosureSubset, Subtype.dist_eq] using hmin ⟨z, mem_spanClosure_of_mem hz⟩ hz
    have hiff' :
        dist (v : 𝓗) (p : 𝓗) = Metric.infDist (v : 𝓗) C ↔
          ∀ z ∈ C, dist (v : 𝓗) (p : 𝓗) ≤ dist (v : 𝓗) z :=
      dist_eq_infDist_iff_forall_dist_le hp
    exact hiff'.mpr hmin'
  · intro h
    have hiff :
        dist (v : 𝓗) (p : 𝓗) = Metric.infDist (v : 𝓗) C ↔
          ∀ z ∈ C, dist (v : 𝓗) (p : 𝓗) ≤ dist (v : 𝓗) z :=
      dist_eq_infDist_iff_forall_dist_le hp
    have hmin : ∀ z ∈ C, dist (v : 𝓗) (p : 𝓗) ≤ dist (v : 𝓗) z :=
      hiff.mp h
    have hmin' : ∀ z ∈ spanClosureSubset C, dist v p ≤ dist v z := by
      -- A subtype competitor is already an ambient competitor lying in `C`.
      intro z hz
      simpa [spanClosureSubset, Subtype.dist_eq] using hmin (z : 𝓗) hz
    have hiff' :
        dist v p = Metric.infDist v (spanClosureSubset C) ↔
          ∀ z ∈ spanClosureSubset C, dist v p ≤ dist v z :=
      dist_eq_infDist_iff_forall_dist_le hp
    exact hiff'.mpr hmin'

-- Proof sketch: let `V := (Submodule.span ℝ C).topologicalClosure`. Since `C ⊆ V`, every
-- `z ∈ C` lies in `V`, while
-- `x - V.starProjection x ∈ Vᗮ` and `V.starProjection x - z ∈ V`. The Pythagorean identity then
-- gives `‖x - z‖ ^ 2 = ‖V.starProjection x - z‖ ^ 2 + ‖x - V.starProjection x‖ ^ 2`, so the
-- minimizing points in `C` for `x` and for `V.starProjection x` coincide. For the consequent,
-- use this equality of projector values together with `V.starProjection x ∈ V` and the fact that
-- `C`, viewed inside `V`, has the same distance-realizing points as in the ambient space.

/-- Proposition 3.25: the set-valued projector onto `C` is unchanged after orthogonal projection
onto the closed span of `C`, and consequently `C` is proximinal in the ambient Hilbert space if
and only if it is proximinal in its closed span. -/
theorem setValuedProjector_eq_comp_closedSpanProjection_and_isProximinalIn_iff
    (C : Set 𝓗) (hC : C.Nonempty) :
    setValuedProjector C =
        setValuedProjector C ∘ ((Submodule.span ℝ C).topologicalClosure).starProjection ∧
      (IsProximinalIn C ↔
        IsProximinalIn (Subtype.val ⁻¹' C : Set ((Submodule.span ℝ C).topologicalClosure))) := by
  let _ : C.Nonempty := hC
  let V : Submodule ℝ 𝓗 := (Submodule.span ℝ C).topologicalClosure
  let C' : Set V := Subtype.val ⁻¹' C
  have hprojector :
      setValuedProjector C = setValuedProjector C ∘ V.starProjection := by
    funext x
    ext p
    rw [Function.comp_apply, mem_setValuedProjector_iff, mem_setValuedProjector_iff]
    constructor
    · intro hp
      have hpmin : ∀ z ∈ C, dist x (p : 𝓗) ≤ dist x z :=
        (dist_eq_infDist_iff_forall_dist_le hp.1).mp hp.2
      have hpV : p ∈ V := by
        simpa [V] using mem_spanClosure_of_mem hp.1
      have hprojmin :
          ∀ z ∈ C, dist (V.starProjection x) p ≤ dist (V.starProjection x) z := by
        -- Each comparison point in `C` lies in the closed span, so the residual term cancels.
        intro z hz
        have hzV : z ∈ V := by
          simpa [V] using mem_spanClosure_of_mem hz
        simpa [V] using (projection_dist_le_iff C hpV hzV).mp (hpmin z hz)
      exact ⟨hp.1, (dist_eq_infDist_iff_forall_dist_le hp.1).mpr hprojmin⟩
    · intro hp
      have hpmin : ∀ z ∈ C, dist (V.starProjection x) p ≤ dist (V.starProjection x) z :=
        (dist_eq_infDist_iff_forall_dist_le hp.1).mp hp.2
      have hpV : p ∈ V := by
        simpa [V] using mem_spanClosure_of_mem hp.1
      have hxmin : ∀ z ∈ C, dist x p ≤ dist x z := by
        -- The same comparison equivalence transports minimality back to the ambient space.
        intro z hz
        have hzV : z ∈ V := by
          simpa [V] using mem_spanClosure_of_mem hz
        simpa [V] using (projection_dist_le_iff C hpV hzV).mpr (hpmin z hz)
      exact ⟨hp.1, (dist_eq_infDist_iff_forall_dist_le hp.1).mpr hxmin⟩
  refine ⟨by simpa [V] using hprojector, ?_⟩
  constructor
  · intro hprox v
    obtain ⟨p, hpC, hpdist⟩ := hprox v
    let q : V := ⟨p, by simpa [V] using mem_spanClosure_of_mem hpC⟩
    -- An ambient minimizer already lives in the closed span and remains minimizing there.
    refine ⟨q, hpC, ?_⟩
    simpa [C', V] using (dist_eq_infDist_spanClosureSubset_iff_ambient C hpC).2 hpdist
  · intro hprox x
    let v : V := V.orthogonalProjection x
    obtain ⟨q, hqC, hqdist⟩ := hprox v
    have hqProj : (q : 𝓗) ∈ setValuedProjector C (V.starProjection x) := by
      -- The closed-span witness yields an ambient best approximation at the projected point.
      rw [mem_setValuedProjector_iff]
      exact ⟨hqC, by
        simpa [C', V, v] using (dist_eq_infDist_spanClosureSubset_iff_ambient C hqC).1 hqdist⟩
    have hqX : (q : 𝓗) ∈ setValuedProjector C x := by
      -- The projector identity lifts that witness back from `P_V x` to `x`.
      rw [(congrFun hprojector x)]
      exact hqProj
    exact ⟨q, (mem_setValuedProjector_iff).mp hqX⟩
end Complete
