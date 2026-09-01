import Mathlib
import Foundation.Hilbert.WeakTopology
import Foundation.Topology.Sequences
import Foundation.Metric.FixedPoint

/-!
# Hilbert WeakConvergence

Weak convergence of sequences, weak cluster points, Opial-type lemmas, and orthonormal sequence examples.
-/

open _root_.LinearMap
open scoped InnerProductSpace
open Filter
open scoped Topology InnerProductSpace
open scoped Topology
open scoped Pointwise
open scoped Topology Pointwise

/-! Source item: Chap02/Example_2_32_1 -/

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Example 2.32.1: every fixed coordinate of an orthonormal sequence tends to `0`. -/
private lemma orthonormal_inner_right_tendsto_zero (x : ℕ → H) (hx : Orthonormal ℝ x) (u : H) :
    Tendsto (fun n ↦ ⟪x n, u⟫_ℝ) atTop (nhds 0) := by
  -- Bessel's inequality makes the squared coordinates summable, so they vanish at infinity.
  have hs : Summable (fun n ↦ ‖⟪x n, u⟫_ℝ‖ ^ 2) :=
    hx.inner_products_summable u
  have hs0 : Tendsto (fun n ↦ ‖⟪x n, u⟫_ℝ‖ ^ 2) atTop (nhds 0) :=
    hs.tendsto_atTop_zero
  -- Taking square roots recovers the norms of the coordinates.
  have hsqrt : Tendsto (fun n ↦ Real.sqrt (‖⟪x n, u⟫_ℝ‖ ^ 2)) atTop
      (nhds (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp hs0
  have hnorm : Tendsto (fun n ↦ ‖⟪x n, u⟫_ℝ‖) atTop (nhds 0) := by
    convert hsqrt using 1
    · ext n
      rw [Real.sqrt_sq]
      positivity
    · simp
  -- Norm convergence to `0` is equivalent to convergence to `0` in `ℝ`.
  exact (tendsto_zero_iff_norm_tendsto_zero).2 hnorm

/-- Example 2.32.1: an orthonormal sequence in a real Hilbert space converges weakly to `0`. -/
-- Proof sketch: for each `u : H`, Bessel's inequality implies that
-- `n ↦ ‖inner ℝ (x n) u‖ ^ 2` is summable, so `inner ℝ (x n) u → 0`. By the Hilbert-space
-- description of the weak topology from Remark 2.31, this is exactly convergence to `0` in
-- `WeakSpace ℝ H`.
theorem orthonormal_sequence_tendsto_zero_weakly (x : ℕ → H) (hx : Orthonormal ℝ x) :
    Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (nhds (0 : WeakSpace ℝ H)) := by
  simpa using
    (weakConvergence_iff_forall_tendsto_inner_right x (0 : H)).2
      fun u ↦ by simpa using orthonormal_inner_right_tendsto_zero x hx u

omit [CompleteSpace H] in
/-- An orthonormal sequence does not converge strongly to `0`. -/
-- Proof sketch: if `x` converged to `0` in norm, then `‖x n‖ → 0`; this contradicts the fact
-- that every term has norm `1`.
theorem orthonormal_sequence_not_tendsto_zero_strongly (x : ℕ → H) (hx : Orthonormal ℝ x) :
    ¬ Tendsto x atTop (nhds (0 : H)) := by
  intro hx0
  -- Strong convergence to `0` forces the norms to converge to `0`.
  have hnorm : Tendsto (fun n ↦ ‖x n‖) atTop (nhds 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).mp hx0
  -- Rewriting the norms with orthonormality turns this into the impossible limit `1 → 0`.
  have hconst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 0) := by
    convert hnorm using 1
    ext n
    simp [hx.norm_eq_one]
  have hconst' : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hone : (0 : ℝ) = 1 :=
    tendsto_nhds_unique hconst hconst'
  norm_num at hone

omit [CompleteSpace H] in
/-- Helper for Example 2.32.1: distinct terms of an orthonormal sequence have squared distance `2`.
-/
private lemma orthonormal_norm_sub_sq_eq_two (x : ℕ → H) (hx : Orthonormal ℝ x) {m n : ℕ}
    (hmn : m ≠ n) :
    ‖x m - x n‖ ^ 2 = 2 := by
  -- Expand the squared norm and simplify the two norm terms and the cross term separately.
  rw [norm_sub_sq_real]
  have hm : ‖x m‖ = 1 := hx.norm_eq_one m
  have hn : ‖x n‖ = 1 := hx.norm_eq_one n
  have hinner : inner ℝ (x m) (x n) = 0 := hx.inner_eq_zero hmn
  nlinarith [hm, hn, hinner]

omit [CompleteSpace H] in
/-- An orthonormal sequence has no Cauchy subsequence. -/
-- Proof sketch: for distinct `m` and `n`, orthonormality gives
-- `‖x m - x n‖ ^ 2 = ‖x m‖ ^ 2 + ‖x n‖ ^ 2 = 2`, so distinct subsequence terms stay a fixed
-- positive distance apart and cannot satisfy the Cauchy criterion.
theorem orthonormal_sequence_not_exists_cauchy_subsequence (x : ℕ → H) (hx : Orthonormal ℝ x) :
    ¬ ∃ φ : ℕ → ℕ, StrictMono φ ∧ CauchySeq (x ∘ φ) := by
  rintro ⟨φ, hφ, hcauchy⟩
  -- A Cauchy subsequence would eventually have all later terms within distance `1` of one anchor.
  rcases (Metric.cauchySeq_iff'.1 hcauchy) 1 zero_lt_one with ⟨N, hN⟩
  have hdist : dist ((x ∘ φ) (N + 1)) ((x ∘ φ) N) < 1 :=
    hN (N + 1) (Nat.le_succ N)
  -- Consecutive subsequence terms are still distinct, so orthonormality keeps them separated.
  have hsq : ‖x (φ (N + 1)) - x (φ N)‖ ^ 2 = 2 := by
    apply orthonormal_norm_sub_sq_eq_two x hx
    exact (hφ (Nat.lt_succ_self N)).ne'
  rw [dist_eq_norm] at hdist
  have hsq_lt : ‖x (φ (N + 1)) - x (φ N)‖ ^ 2 < 1 := by
    simpa using
      (pow_lt_pow_left₀ hdist (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0))
  linarith

/-! Source item: Chap02/Example_2_32_2 -/


-- Proof sketch: the norm is continuous for the strong topology, so the unit sphere is the
-- preimage of the closed set `{1}` under `x ↦ ‖x‖`, hence strongly closed. For the weak statement,
-- choose an orthonormal sequence in the infinite-dimensional Hilbert space; each term lies on the
-- unit sphere and the preceding weak-convergence result shows that this sequence converges weakly
-- to `0`, which does not belong to the sphere.
/-- Helper for Example 2.32.2: every infinite-dimensional real Hilbert space contains an
orthonormal sequence indexed by `ℕ`. -/
lemma exists_orthonormal_sequence_of_not_finiteDimensional
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    (h_infinite : ¬ FiniteDimensional ℝ 𝓗) :
    ∃ e : ℕ → 𝓗, Orthonormal ℝ e := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℝ 𝓗
  -- A finite Hilbert-basis index set would force finite dimensionality, contradicting the hypothesis.
  have hw_infinite : w.Infinite := by
    by_contra hw_infinite
    have hw_finite : Set.Finite w := (Set.finite_or_infinite w).resolve_right hw_infinite
    haveI : Fintype w := hw_finite.fintype
    have hfd : FiniteDimensional ℝ 𝓗 :=
      Module.Basis.finiteDimensional_of_finite (b.toOrthonormalBasis.toBasis)
    exact h_infinite hfd
  -- Extract a countable orthonormal subfamily by embedding `ℕ` into the infinite basis index set.
  let f : ℕ ↪ w := Set.Infinite.natEmbedding w hw_infinite
  refine ⟨fun n ↦ b (f n), ?_⟩
  simpa [Function.comp] using b.orthonormal.comp f f.injective

/-- Helper for Example 2.32.2: orthonormal vectors lie on the weak unit sphere. -/
private lemma orthonormal_sequence_mem_weak_unitSphere
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    (e : ℕ → 𝓗) (he : Orthonormal ℝ e) :
    ∀ n, toWeakSpace ℝ 𝓗 (e n) ∈
      ((toWeakSpace ℝ 𝓗) '' Metric.sphere (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗)) := by
  intro n
  refine ⟨e n, ?_, rfl⟩
  -- Each term of an orthonormal family has norm `1`.
  simpa [Metric.mem_sphere, dist_eq_norm] using he.norm_eq_one n

/-- Helper for Example 2.32.2: the weak unit sphere excludes the origin. -/
private lemma zero_not_mem_weak_unitSphere
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗] :
    (0 : WeakSpace ℝ 𝓗) ∉
      ((toWeakSpace ℝ 𝓗) '' Metric.sphere (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗)) := by
  -- The origin has norm `0`, so it cannot lie on the norm-one sphere.
  rintro ⟨x, hx, hx0⟩
  have : x = 0 := (toWeakSpace ℝ 𝓗).injective hx0
  subst this
  simp at hx

/-- Example 2.32.2: in an infinite-dimensional real Hilbert space, the image of the unit sphere in
`WeakSpace ℝ 𝓗` is not sequentially closed. -/
theorem not_isSeqClosed_image_unitSphere_toWeakSpace
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    (h_infinite : ¬ FiniteDimensional ℝ 𝓗) :
    ¬ IsSeqClosed (((toWeakSpace ℝ 𝓗) '' Metric.sphere (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗))) := by
  -- Use an orthonormal sequence in the unit sphere converging weakly to `0`.
  intro h_seqClosed
  obtain ⟨e, he⟩ := exists_orthonormal_sequence_of_not_finiteDimensional h_infinite
  have hmem :
      ∀ n, toWeakSpace ℝ 𝓗 (e n) ∈
        ((toWeakSpace ℝ 𝓗) '' Metric.sphere (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗)) :=
    orthonormal_sequence_mem_weak_unitSphere e he
  have hweak :
      Tendsto (fun n ↦ toWeakSpace ℝ 𝓗 (e n)) atTop (𝓝 (0 : WeakSpace ℝ 𝓗)) :=
    orthonormal_sequence_tendsto_zero_weakly e he
  have hzero_mem :
      (0 : WeakSpace ℝ 𝓗) ∈
        ((toWeakSpace ℝ 𝓗) '' Metric.sphere (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗)) :=
    h_seqClosed hmem hweak
  -- Sequential closedness would force the weak limit `0` back into the sphere, contradiction.
  exact zero_not_mem_weak_unitSphere hzero_mem

/-- Example 2.32.2: in an infinite-dimensional real Hilbert space, the unit sphere is closed for
the strong topology, but its image in `WeakSpace ℝ 𝓗` is not sequentially closed. -/
theorem unitSphere_isClosed_in_strongTopology_and_not_seqClosed_in_weakTopology
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    (h_infinite : ¬ FiniteDimensional ℝ 𝓗) :
    IsClosed (Metric.sphere (0 : 𝓗) 1) ∧
      ¬ IsSeqClosed (((toWeakSpace ℝ 𝓗) '' Metric.sphere (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗))) := by
  refine ⟨?_, not_isSeqClosed_image_unitSphere_toWeakSpace h_infinite⟩
  simpa using (Metric.isClosed_sphere : IsClosed (Metric.sphere (0 : 𝓗) (1 : ℝ)))

/-! Source item: Chap02/Lemma_2_41 -/
universe v w


variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- Helper for Lemma 2.41: after transporting to weak spaces, a continuous affine map splits as
its continuous linear part plus the constant translation by its value at `0`. -/
private lemma continuousAffineMap_toWeakSpace_eq_map_add_const (T : H →ᴬ[ℝ] K) :
    (fun x : WeakSpace ℝ H ↦ toWeakSpace ℝ K (T ((toWeakSpace ℝ H).symm x))) =
      fun x : WeakSpace ℝ H ↦ WeakSpace.map T.contLinear x + toWeakSpace ℝ K (T 0) := by
  -- Rewrite the transported affine map using the standard affine decomposition `T = linear + const`.
  funext x
  simpa [WeakSpace.map_apply] using
    congrFun ((T : H →ᵃ[ℝ] K).decomp) ((toWeakSpace ℝ H).symm x)

-- Proof sketch: decompose the continuous affine map `T` as its continuous linear part plus the
-- constant translation by `T 0`; the linear part is weak-to-weak continuous via `WeakSpace.map`,
-- and translation by a fixed vector is a homeomorphism for the weak topology.
/-- Lemma 2.41: a continuous affine map between real normed spaces is continuous from the weak
topology on the domain to the weak topology on the codomain. -/
theorem continuousAffineMap_continuous_toWeakSpace (T : H →ᴬ[ℝ] K) :
    Continuous fun x : WeakSpace ℝ H ↦ toWeakSpace ℝ K (T ((toWeakSpace ℝ H).symm x)) := by
  -- First rewrite the affine map as its weakly continuous linear part plus a fixed translation.
  rw [continuousAffineMap_toWeakSpace_eq_map_add_const]
  -- Then combine continuity of `WeakSpace.map T.contLinear` with continuity of addition by a constant.
  exact (WeakSpace.map T.contLinear).continuous.add continuous_const

-- Proof sketch: apply `continuousAffineMap_continuous_toWeakSpace` to the weakly convergent net
-- and use preservation of `Tendsto` under composition with a continuous map.
/-- A weakly convergent directed net remains weakly convergent after application of a continuous
affine map. -/
theorem continuousAffineMap_tendsto_toWeakSpace
    {A : Type w} [Preorder A] [IsDirectedOrder A] (T : H →ᴬ[ℝ] K) {ξ : A → H} {x : H}
    (hξ : Tendsto (fun a ↦ toWeakSpace ℝ H (ξ a)) atTop (𝓝 (toWeakSpace ℝ H x))) :
    Tendsto (fun a ↦ toWeakSpace ℝ K (T (ξ a))) atTop (𝓝 (toWeakSpace ℝ K (T x))) := by
  -- Push the weak convergence through the continuous map on weak spaces established above.
  have hT :
      Continuous fun y : WeakSpace ℝ H ↦ toWeakSpace ℝ K (T ((toWeakSpace ℝ H).symm y)) :=
    continuousAffineMap_continuous_toWeakSpace T
  exact (hT.tendsto (toWeakSpace ℝ H x)).comp hξ

/-! Source item: Chap02/Lemma_2_43 -/

universe z

namespace LinearMap

variable {A : Type z} [Preorder A]
variable {H : Type u} {G : Type v} {K : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Lemma 2.43: a bilinear map between real Hilbert spaces that satisfies a global norm bound sends
a bounded strongly convergent net in the first variable and a strongly convergent net in the second
variable to a strongly convergent net. -/
-- Proof sketch: the norm bound upgrades `T` to a continuous bilinear map. Joint continuity then
-- gives the convergence of `a ↦ T (x_net a) (u_net a)` directly, so the boundedness assumption on
-- `x_net` is retained only to match the textbook statement.
theorem tendsto_apply_bilinear_of_tendsto_of_bounded_range
    (T : H →ₗ[ℝ] G →ₗ[ℝ] K)
    (hT : ∃ beta : ℝ, 0 < beta ∧ ∀ x u, ‖T x u‖ ≤ beta * ‖x‖ * ‖u‖)
    {x_net : A → H} {u_net : A → G} {x : H} {u : G}
    (_hx_bdd : Bornology.IsBounded (Set.range x_net))
    (hx : Tendsto x_net atTop (nhds x))
    (hu : Tendsto u_net atTop (nhds u)) :
    Tendsto (fun a ↦ T (x_net a) (u_net a)) atTop (nhds (T x u)) := by
  obtain ⟨beta, hbeta_pos, hbeta⟩ := hT
  simpa [LinearMap.mkContinuous₂_apply] using
    ((T.mkContinuous₂ beta hbeta).continuous₂.tendsto (x, u)).comp (hx.prodMk_nhds hu)

end LinearMap

/-! Source item: Chap02/Lemma_2_44 -/


variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {A : Type v} [Preorder A]

/-- Lemma 2.44: in a real Hilbert space, if `xₐ → x` and `uₐ → u` in norm and the net `xₐ` is
bounded, then `inner ℝ (xₐ a) (uₐ a)` converges to `inner ℝ x u`. -/
-- The boundedness hypothesis is part of the source statement. The canonical proof is the stronger
-- mathlib theorem `Filter.Tendsto.inner`, coming from joint continuity of the inner product.
theorem tendsto_inner_of_bounded_left
    {xₐ uₐ : A → H} {x u : H}
    (_hxₐ_bdd : Bornology.IsBounded (Set.range xₐ))
    (hxₐ : Tendsto xₐ atTop (𝓝 x))
    (huₐ : Tendsto uₐ atTop (𝓝 u)) :
    Tendsto (fun a ↦ inner ℝ (xₐ a) (uₐ a)) atTop (𝓝 (inner ℝ x u)) := by
  simpa using Filter.Tendsto.inner hxₐ huₐ

/-! Source item: Chap02/Lemma_2_45 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- The weak image of a scaled closed unit ball agrees with the scalar multiple of the weak image
of the unit ball. -/
private lemma weak_image_smul_closedBall_eq_smul_weak_image_closedBall (r : ℝ) :
    ((toWeakSpace ℝ 𝓗) '' (r • Metric.closedBall (0 : 𝓗) 1)) =
      r • ((toWeakSpace ℝ 𝓗) '' Metric.closedBall (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨y, hy, rfl⟩
    refine ⟨toWeakSpace ℝ 𝓗 y, ?_, ?_⟩
    · exact ⟨y, hy, rfl⟩
    · simp
  · rintro ⟨w, hw, rfl⟩
    rcases hw with ⟨y, hy, rfl⟩
    refine ⟨r • y, ?_, ?_⟩
    · exact ⟨y, hy, rfl⟩
    · simp

variable [CompleteSpace 𝓗]

private lemma weak_image_closedBall_zero_isCompact (r : ℝ) :
    IsCompact ((toWeakSpace ℝ 𝓗) '' Metric.closedBall (0 : 𝓗) r : Set (WeakSpace ℝ 𝓗)) := by
  by_cases hr : 0 ≤ r
  · have hunit :
        IsCompact ((toWeakSpace ℝ 𝓗) '' Metric.closedBall (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗)) :=
      isCompact_unitBall_weakSpace
    have hsmul :
        IsCompact
          (r • ((toWeakSpace ℝ 𝓗) '' Metric.closedBall (0 : 𝓗) 1 : Set (WeakSpace ℝ 𝓗))) :=
      IsCompact.smul r hunit
    rw [← smul_unitClosedBall_of_nonneg hr]
    rw [weak_image_smul_closedBall_eq_smul_weak_image_closedBall]
    exact hsmul
  · rw [Metric.closedBall_of_neg (lt_of_not_ge hr)]
    simp

/-- Helper for Lemma 2.45: every closed ball centered at `0` is weakly sequentially compact in a
real Hilbert space. -/
theorem weak_image_closedBall_zero_isSeqCompact (r : ℝ) :
    IsSeqCompact ((toWeakSpace ℝ 𝓗) '' Metric.closedBall (0 : 𝓗) r : Set (WeakSpace ℝ 𝓗)) := by
  exact
    (weaklyCompact_iff_weaklySeqCompact (Metric.closedBall (0 : 𝓗) r)).mp
      (weak_image_closedBall_zero_isCompact r)

/-- Lemma 2.45: every bounded sequence in a real Hilbert space admits a weakly convergent
subsequence. Here weak convergence is expressed by convergence in `WeakSpace ℝ 𝓗`. -/
-- Proof sketch: bound the range of the sequence inside a closed ball centered at `0`, use weak
-- compactness of that ball, convert it to weak sequential compactness via Eberlein-Smulian, and
-- then apply the subsequence characterization of sequential compactness in the weak topology.
theorem bounded_sequence_has_weakly_convergent_subsequence
    (x : ℕ → 𝓗) (hx : Bornology.IsBounded (Set.range x)) :
    ∃ y : 𝓗, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k ↦ toWeakSpace ℝ 𝓗 (x (φ k))) atTop (𝓝 (toWeakSpace ℝ 𝓗 y)) := by
  obtain ⟨r, hsubset⟩ := hx.subset_closedBall (0 : 𝓗)
  have hseqCompactAmbient :
      IsSeqCompact ((toWeakSpace ℝ 𝓗) '' Metric.closedBall (0 : 𝓗) r : Set (WeakSpace ℝ 𝓗)) :=
    weak_image_closedBall_zero_isSeqCompact r
  have hx_mem :
      ∀ n, toWeakSpace ℝ 𝓗 (x n) ∈
        ((toWeakSpace ℝ 𝓗) '' Metric.closedBall (0 : 𝓗) r : Set (WeakSpace ℝ 𝓗)) := by
    intro n
    refine ⟨x n, hsubset (Set.mem_range_self n), rfl⟩
  obtain ⟨w, hw, φ, hφ, hconv⟩ := hseqCompactAmbient hx_mem
  rcases hw with ⟨y, hy, rfl⟩
  refine ⟨y, φ, hφ, ?_⟩
  simpa [Function.comp] using hconv

/-! Source item: Chap02/Lemma_2_46 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- A weakly convergent sequence has no weak sequential cluster point other than its weak limit. -/
private lemma weak_cluster_point_eq_of_tendsto
    {x : ℕ → 𝓗} {y z : 𝓗}
    (hy : Tendsto (fun n ↦ toWeakSpace ℝ 𝓗 (x n)) atTop (𝓝 (toWeakSpace ℝ 𝓗 y)))
    (hz : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ 𝓗 (x n)) (toWeakSpace ℝ 𝓗 z)) :
    z = y := by
  rcases hz.exists_subseq_tendsto with ⟨φ, hφ, hφz⟩
  -- A strictly increasing subsequence of a convergent sequence has the same weak limit.
  have hφy :
      Tendsto (fun n ↦ toWeakSpace ℝ 𝓗 (x (φ n))) atTop (𝓝 (toWeakSpace ℝ 𝓗 y)) := by
    simpa [Function.comp] using hy.comp hφ.tendsto_atTop
  -- Hausdorffness of the weak topology identifies the two subsequential limits.
  have hEq : toWeakSpace ℝ 𝓗 z = toWeakSpace ℝ 𝓗 y :=
    tendsto_nhds_unique hφz hφy
  exact (toWeakSpace ℝ 𝓗).injective hEq

variable [CompleteSpace 𝓗]

/-- Helper for Lemma 2.46: weak convergence of a sequence in a real Hilbert space forces its range
to be norm-bounded. -/
lemma bounded_range_of_tendsto_weakly
    {x : ℕ → 𝓗} {y : 𝓗}
    (hy : Tendsto (fun n ↦ toWeakSpace ℝ 𝓗 (x n)) atTop (𝓝 (toWeakSpace ℝ 𝓗 y))) :
    Bornology.IsBounded (Set.range x) := by
  let T : ℕ → 𝓗 →L[ℝ] ℝ := fun n ↦ InnerProductSpace.toDual ℝ 𝓗 (x n)
  have hpointwise : ∀ u : 𝓗, ∃ C : ℝ, ∀ n : ℕ, ‖T n u‖ ≤ C := by
    intro u
    -- Weak convergence gives convergence of each scalar inner-product coordinate.
    have hu_tendsto :
        Tendsto (fun n ↦ inner ℝ (x n) u) atTop (𝓝 (inner ℝ y u)) := by
      simpa using
        (weakSpace_continuous_inner_right u).tendsto (toWeakSpace ℝ 𝓗 y) |>.comp hy
    have hu_bounded :
        Bornology.IsBounded (Set.range fun n ↦ inner ℝ (x n) u) :=
      Metric.isBounded_range_of_tendsto _ hu_tendsto
    rcases isBounded_iff_forall_norm_le.mp hu_bounded with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro n
    have hCn : ‖inner ℝ (x n) u‖ ≤ C := hC _ (Set.mem_range_self n)
    simpa [T, InnerProductSpace.toDual_apply_apply] using hCn
  -- Banach-Steinhaus upgrades the pointwise bounds to a uniform norm bound.
  obtain ⟨C, hC⟩ := uniform_boundedness_principle hpointwise
  rw [isBounded_iff_forall_norm_le]
  refine ⟨C, ?_⟩
  rintro z ⟨n, rfl⟩
  have hTn : ‖T n‖ ≤ C := hC n
  change ‖InnerProductSpace.toDual ℝ 𝓗 (x n)‖ ≤ C at hTn
  rw [(InnerProductSpace.toDual ℝ 𝓗).norm_map] at hTn
  exact hTn

/-- A bounded sequence in a real Hilbert space lies in a weakly sequentially compact ambient set. -/
private lemma weak_seq_compact_ambient_of_bounded_range
    {x : ℕ → 𝓗} (hx : Bornology.IsBounded (Set.range x)) :
    ∃ C : Set (WeakSpace ℝ 𝓗), IsSeqCompact C ∧
      ∀ n, toWeakSpace ℝ 𝓗 (x n) ∈ C := by
  obtain ⟨r, hsubset⟩ := hx.subset_closedBall (0 : 𝓗)
  let C : Set (WeakSpace ℝ 𝓗) := (toWeakSpace ℝ 𝓗) '' Metric.closedBall (0 : 𝓗) r
  have hC : IsSeqCompact C := by
    simpa [C] using weak_image_closedBall_zero_isSeqCompact r
  have hx_mem : ∀ n, toWeakSpace ℝ 𝓗 (x n) ∈ C := by
    intro n
    exact ⟨x n, hsubset (Set.mem_range_self n), rfl⟩
  exact ⟨C, hC, hx_mem⟩

/-- Lemma 2.46: a sequence in a real Hilbert space converges weakly if and only if its range is
norm-bounded and it has at most one weak sequential cluster point. The weak convergence and weak
cluster-point conditions are expressed in the canonical weak topology `WeakSpace ℝ 𝓗`. -/
-- Proof sketch: if `x` converges weakly to `y`, every weakly convergent subsequence has the same
-- weak limit by Hausdorffness of `WeakSpace ℝ 𝓗`, and boundedness follows from pointwise bounded
-- inner-product functionals via uniform boundedness. Conversely, boundedness places the range of
-- `x` inside a weakly sequentially compact set, so existence of a weak sequential cluster point
-- follows from weak compactness and Eberlein-Smulian; uniqueness of that cluster point then yields
-- weak convergence of the whole sequence by the Hausdorff sequential-compactness criterion.
theorem weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint
    (x : ℕ → 𝓗) :
    (∃ y : 𝓗, Tendsto (fun n ↦ toWeakSpace ℝ 𝓗 (x n)) atTop (𝓝 (toWeakSpace ℝ 𝓗 y))) ↔
      Bornology.IsBounded (Set.range x) ∧
        ∀ y z : 𝓗,
          IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ 𝓗 (x n)) (toWeakSpace ℝ 𝓗 y) →
          IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ 𝓗 (x n)) (toWeakSpace ℝ 𝓗 z) →
          y = z := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨bounded_range_of_tendsto_weakly hy, ?_⟩
    intro z w hz hw
    -- Every weak cluster point must agree with the weak limit of the full sequence.
    calc
      z = y := weak_cluster_point_eq_of_tendsto hy hz
      _ = w := (weak_cluster_point_eq_of_tendsto hy hw).symm
  · rintro ⟨hx_bounded, hx_unique⟩
    rcases weak_seq_compact_ambient_of_bounded_range hx_bounded with ⟨C, hC, hxC⟩
    rcases bounded_sequence_has_weakly_convergent_subsequence x hx_bounded with
      ⟨y, φ, hφ, hφ_tendsto⟩
    have hy_cluster :
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ 𝓗 (x n)) (toWeakSpace ℝ 𝓗 y) :=
      ⟨φ, hφ, hφ_tendsto⟩
    refine ⟨y, ?_⟩
    -- Lemma 1.35 turns uniqueness of weak-space sequential cluster points into convergence.
    refine tendsto_of_unique_sequential_cluster_point hC hxC ?_
    intro w hw
    -- Translate a weak-space cluster point back to the original Hilbert space.
    have hw_cluster :
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ 𝓗 (x n))
          (toWeakSpace ℝ 𝓗 ((toWeakSpace ℝ 𝓗).symm w)) := by
      rcases hw.exists_subseq_tendsto with ⟨ψ, hψ, hψ_tendsto⟩
      exact ⟨ψ, hψ, by simpa [Function.comp] using hψ_tendsto⟩
    have hw_eq : (toWeakSpace ℝ 𝓗).symm w = y :=
      hx_unique _ _ hw_cluster hy_cluster
    simpa using congrArg (toWeakSpace ℝ 𝓗) hw_eq

/-! Source item: Chap02/Lemma_2_47 -/


variable {H : Type u}

/-- Helper for Lemma 2.47: convergence of the distances to one reference point forces the whole
sequence to be norm-bounded. -/
lemma bounded_range_of_convergent_distance_to_point [NormedAddCommGroup H] {x : ℕ → H} {z : H}
    (hz : ∃ l : ℝ, Tendsto (fun n ↦ ‖x n - z‖) atTop (𝓝 l)) :
    Bornology.IsBounded (Set.range x) := by
  rcases hz with ⟨l, hl⟩
  have hdist_bounded :
      Bornology.IsBounded (Set.range fun n ↦ ‖x n - z‖) :=
    Metric.isBounded_range_of_tendsto _ hl
  rcases isBounded_iff_forall_norm_le.mp hdist_bounded with ⟨R, hR⟩
  rw [isBounded_iff_forall_norm_le]
  refine ⟨R + ‖z‖, ?_⟩
  rintro y ⟨n, rfl⟩
  have hRn : ‖x n - z‖ ≤ R := by
    simpa using hR _ (Set.mem_range_self n)
  -- Compare `x n` with the translated point `(x n - z) + z`.
  calc
    ‖x n‖ = ‖(x n - z) + z‖ := by abel_nf
    _ ≤ ‖x n - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ R + ‖z‖ := by simpa [add_comm] using add_le_add_right hRn ‖z‖

/-- Helper for Lemma 2.47: convergence of the distance sequences to two points of `C` forces
convergence of the corresponding inner-product coordinate sequence. -/
lemma inner_tendsto_of_tendsto_dist_to_two_points [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {C : Set H} {x : ℕ → H}
    (hdist : ∀ w ∈ C, ∃ l : ℝ, Tendsto (fun n ↦ ‖x n - w‖) atTop (𝓝 l))
    {y z : H} (hy : y ∈ C) (hz : z ∈ C) :
    ∃ l : ℝ, Tendsto (fun n ↦ inner ℝ (x n) (y - z)) atTop (𝓝 l) := by
  rcases hdist y hy with ⟨ly, hly⟩
  rcases hdist z hz with ⟨lz, hlz⟩
  refine ⟨(lz ^ 2 - ly ^ 2 + ‖y‖ ^ 2 - ‖z‖ ^ 2) / 2, ?_⟩
  have hTwoInnerEq :
      (fun n ↦ 2 * inner ℝ (x n) (y - z)) =
        (fun n ↦ ‖x n - z‖ ^ 2 - ‖x n - y‖ ^ 2 + ‖y‖ ^ 2 - ‖z‖ ^ 2) := by
    funext n
    -- Expand both squared distances and collect the inner-product terms.
    rw [norm_sub_sq_real, norm_sub_sq_real, inner_sub_right]
    ring_nf
  have hTwoInner :
      Tendsto (fun n ↦ 2 * inner ℝ (x n) (y - z)) atTop
        (𝓝 (lz ^ 2 - ly ^ 2 + ‖y‖ ^ 2 - ‖z‖ ^ 2)) := by
    rw [hTwoInnerEq]
    have hConst :
        Tendsto (fun _ : ℕ ↦ ‖y‖ ^ 2 - ‖z‖ ^ 2) atTop (𝓝 (‖y‖ ^ 2 - ‖z‖ ^ 2)) :=
      tendsto_const_nhds
    -- The polarization identity writes the coordinate as a linear combination of convergent
    -- squared-distance sequences.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      ((hlz.pow 2).sub (hly.pow 2)).add hConst
  have hHalf :
      Tendsto (fun n ↦ (1 / 2 : ℝ) * (2 * inner ℝ (x n) (y - z))) atTop
        (𝓝 ((1 / 2 : ℝ) * (lz ^ 2 - ly ^ 2 + ‖y‖ ^ 2 - ‖z‖ ^ 2))) :=
    hTwoInner.const_mul (1 / 2 : ℝ)
  -- Dividing the convergent double-inner-product sequence by `2` gives the desired limit.
  convert hHalf using 1 <;> ring_nf

/-- Helper for Lemma 2.47: two weak sequential cluster points must coincide once all distance
sequences on `C` converge. -/
lemma weak_cluster_point_eq_of_convergent_distances [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {C : Set H} {x : ℕ → H}
    (hdist : ∀ w ∈ C, ∃ l : ℝ, Tendsto (fun n ↦ ‖x n - w‖) atTop (𝓝 l))
    (hcluster :
      ∀ w : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H w) → w ∈ C)
    {y z : H}
    (hy : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H y))
    (hz : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H z)) :
    y = z := by
  have hyC : y ∈ C := hcluster y hy
  have hzC : z ∈ C := hcluster z hz
  rcases inner_tendsto_of_tendsto_dist_to_two_points hdist hyC hzC with ⟨l, hl⟩
  rcases hy with ⟨φ, hφ, hφ_tendsto⟩
  rcases hz with ⟨ψ, hψ, hψ_tendsto⟩
  have hφ_limit :
      Tendsto (fun n ↦ inner ℝ (x (φ n)) (y - z)) atTop (𝓝 (inner ℝ y (y - z))) := by
    -- Weak convergence of the `φ`-subsequence controls the coordinate against `y - z`.
    simpa using
      (weakSpace_continuous_inner_right (y - z)).tendsto (toWeakSpace ℝ H y) |>.comp
        hφ_tendsto
  have hψ_limit :
      Tendsto (fun n ↦ inner ℝ (x (ψ n)) (y - z)) atTop (𝓝 (inner ℝ z (y - z))) := by
    -- The same coordinate along the `ψ`-subsequence converges to the corresponding `z`-value.
    simpa using
      (weakSpace_continuous_inner_right (y - z)).tendsto (toWeakSpace ℝ H z) |>.comp
        hψ_tendsto
  have hy_limit_eq : inner ℝ y (y - z) = l := by
    exact tendsto_nhds_unique hφ_limit (hl.comp hφ.tendsto_atTop)
  have hz_limit_eq : inner ℝ z (y - z) = l := by
    exact tendsto_nhds_unique hψ_limit (hl.comp hψ.tendsto_atTop)
  have hzero_sq : ‖y - z‖ ^ 2 = 0 := by
    -- The two subsequential limits agree, so the self-inner-product of `y - z` vanishes.
    calc
      ‖y - z‖ ^ 2 = inner ℝ (y - z) (y - z) := by rw [real_inner_self_eq_norm_sq]
      _ = inner ℝ y (y - z) - inner ℝ z (y - z) := by rw [inner_sub_left]
      _ = 0 := by rw [hy_limit_eq, hz_limit_eq, sub_self]
  have hzero : ‖y - z‖ = 0 := sq_eq_zero_iff.mp hzero_sq
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- Lemma 2.47: if `C` is a nonempty subset of a real Hilbert space, the distance sequence
`n ↦ ‖x n - z‖` converges for every `z ∈ C`, and every weak sequential cluster point of `x`
belongs to `C`, then `x` converges weakly in `WeakSpace ℝ H` to some point of `C`. The
cluster-point hypothesis is expressed by `IsSequentialClusterPt` in the canonical weak topology
`WeakSpace ℝ H`. -/
-- Proof sketch: first use nonemptiness of `C` and convergence of one distance sequence to deduce
-- that `x` is bounded. Then apply weak sequential compactness to obtain a weakly convergent
-- subsequence. The cluster-point hypothesis puts every weak sequential cluster point in `C`, and
-- the convergence of all distance sequences on `C` gives uniqueness of such cluster points by the
-- standard polarization identity. Finally conclude that the whole sequence converges weakly to that
-- unique cluster point.
theorem opial_lemma [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {C : Set H} (hC : C.Nonempty) (x : ℕ → H)
    (hdist : ∀ z ∈ C, ∃ l : ℝ, Tendsto (fun n ↦ ‖x n - z‖) atTop (𝓝 l))
    (hcluster :
      ∀ z : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H z) → z ∈ C) :
    ∃ z ∈ C, Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H z)) := by
  rcases hC with ⟨z₀, hz₀⟩
  have hx_bounded : Bornology.IsBounded (Set.range x) := by
    exact bounded_range_of_convergent_distance_to_point (hdist z₀ hz₀)
  have hx_unique :
      ∀ y z : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H y) →
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H z) →
        y = z := by
    intro y z hy hz
    exact weak_cluster_point_eq_of_convergent_distances hdist hcluster hy hz
  rcases
      (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint x).2
        ⟨hx_bounded, hx_unique⟩ with
    ⟨z, hz⟩
  have hz_cluster :
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (x n)) (toWeakSpace ℝ H z) := by
    exact ⟨id, strictMono_id, by simpa using hz⟩
  exact ⟨z, hcluster z hz_cluster, hz⟩

/-! Source item: Chap02/Proposition_2_48 -/


variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Proposition 2.48: if a sequence in a real Hilbert space is asymptotic in norm to an
orthonormal sequence, then it converges weakly to `0`. -/
-- Proof sketch: Example 2.32.1 gives weak convergence of the orthonormal comparison sequence to
-- `0`. The perturbation `x n - y n` converges strongly to `0` because its norm tends to `0`, so
-- its image in `WeakSpace ℝ H` also converges to `0`. Adding the two weakly null sequences yields
-- the result.
theorem tendsto_zero_weakly_of_orthonormal_of_norm_sub_tendsto_zero
    (x y : ℕ → H) (hy : Orthonormal ℝ y)
    (hxy : Tendsto (fun n ↦ ‖x n - y n‖) atTop (nhds (0 : ℝ))) :
    Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (nhds (0 : WeakSpace ℝ H)) := by
  have hyWeak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (y n)) atTop (nhds (0 : WeakSpace ℝ H)) :=
    orthonormal_sequence_tendsto_zero_weakly y hy
  have hsubStrong : Tendsto (fun n ↦ x n - y n) atTop (nhds (0 : H)) := by
    simpa using (tendsto_zero_iff_norm_tendsto_zero).2 hxy
  have hsubWeak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (x n - y n)) atTop (nhds (0 : WeakSpace ℝ H)) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto 0).comp hsubStrong
  have hsum :
      Tendsto (fun n ↦ toWeakSpace ℝ H (x n - y n) + toWeakSpace ℝ H (y n))
        atTop (nhds (0 + 0 : WeakSpace ℝ H)) :=
    hsubWeak.add hyWeak
  simpa [sub_add_cancel] using hsum

/-! Source item: Chap02/Proposition_2_49 -/


variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- An asymptotic orthonormal subsequence of `x` is a strictly monotone reindexing of `x`
together with an orthonormal sequence that approximates the reindexed sequence in norm. -/
private structure AsymptoticOrthonormalSubsequence (x : ℕ → H) where
  /-- The subsequence extraction map. -/
  subseq : ℕ → ℕ
  /-- The extraction map is strictly monotone. -/
  strictMono_subseq : StrictMono subseq
  /-- The orthonormal comparison sequence. -/
  orthonormalSeq : ℕ → H
  /-- The comparison sequence is orthonormal. -/
  orthonormal_orthonormalSeq : Orthonormal ℝ orthonormalSeq
  /-- The reindexed sequence is asymptotic in norm to the orthonormal comparison sequence. -/
  tendsto_sub_orthonormalSeq :
    Tendsto (fun n ↦ x (subseq n) - orthonormalSeq n) atTop (nhds (0 : H))

/-- Helper for Proposition 2.49: every fixed inner-product coordinate of a weakly null sequence
also tends to `0`. -/
-- Proof sketch: apply the weak-topology characterization to the Fréchet-Riesz functional
-- represented by the testing vector.
private lemma weak_tendsto_zero_inner_right (x : ℕ → H)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (nhds (0 : WeakSpace ℝ H))) (u : H) :
    Tendsto (fun n ↦ inner ℝ u (x n)) atTop (nhds 0) := by
  -- Evaluate weak convergence through the canonical inner-product characterization of Remark 2.31.
  have hx' : Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (nhds (toWeakSpace ℝ H (0 : H))) := by
    simpa using hx
  have hu :
      Tendsto (fun n ↦ inner ℝ (x n) u) atTop (nhds (inner ℝ (0 : H) u)) :=
    (weakConvergence_iff_forall_tendsto_inner_right x (0 : H)).1 hx' u
  simpa [real_inner_comm] using hu

/-- Helper for Proposition 2.49: for a finite family of test vectors, weak convergence yields a far
tail index where all inner products are simultaneously small. -/
-- Proof sketch: bundle the finitely many coordinates into a single map
-- `ℕ → (Fin (n + 1) → ℝ)`, use convergence to `0` in the finite product, then read each
-- coordinate bound from the norm bound.
private lemma exists_far_index_with_small_inner_family (x : ℕ → H)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (nhds (0 : WeakSpace ℝ H)))
    (y : Fin (n + 1) → H) (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m > N, ∀ i, |inner ℝ (y i) (x m)| < δ := by
  have hall : ∀ᶠ m in atTop, ∀ i, |inner ℝ (y i) (x m)| < δ := by
    -- Build the simultaneous estimate by induction on the finite index family.
    induction n with
    | zero =>
        have hcoord : Tendsto (fun m ↦ inner ℝ (y 0) (x m)) atTop (nhds 0) :=
          weak_tendsto_zero_inner_right x hx (y 0)
        have habs : Tendsto (fun m ↦ |inner ℝ (y 0) (x m)|) atTop (nhds 0) := by
          simpa [Real.norm_eq_abs] using (tendsto_zero_iff_norm_tendsto_zero).1 hcoord
        filter_upwards [habs.eventually (eventually_lt_nhds hδ)] with m hm i
        fin_cases i
        simpa using hm
    | succ n ih =>
        have hlast_coord :
            Tendsto (fun m ↦ inner ℝ (y (Fin.last (n + 1))) (x m)) atTop (nhds 0) :=
          weak_tendsto_zero_inner_right x hx (y (Fin.last (n + 1)))
        have hlast_abs :
            Tendsto (fun m ↦ |inner ℝ (y (Fin.last (n + 1))) (x m)|) atTop (nhds 0) := by
          simpa [Real.norm_eq_abs] using (tendsto_zero_iff_norm_tendsto_zero).1 hlast_coord
        have hinit :
            ∀ᶠ m in atTop, ∀ i : Fin (n + 1), |inner ℝ ((Fin.init y) i) (x m)| < δ :=
          ih (Fin.init y)
        filter_upwards [hlast_abs.eventually (eventually_lt_nhds hδ), hinit] with m hm_last hm_init i
        cases i using Fin.lastCases with
        | last =>
            simpa using hm_last
        | cast j =>
            simpa using hm_init j
  rcases (hall.and (eventually_gt_atTop N)).exists with ⟨m, hm_small, hm_gt⟩
  exact ⟨m, hm_gt, hm_small⟩

omit [CompleteSpace H] in
/-- Helper for Proposition 2.49: normalizing a nonzero vector perturbs a unit vector by at most
twice the pre-normalization error. -/
-- Proof sketch: first compare `x` to the unnormalized vector `v`, then compare `v` to its
-- normalization using the reverse triangle inequality on the norms.
private lemma norm_sub_normalized_block_le_twice {x v : H} (hx : ‖x‖ = 1) (hv : v ≠ 0) :
    ‖x - (‖v‖)⁻¹ • v‖ ≤ 2 * ‖x - v‖ := by
  let y : H := (‖v‖)⁻¹ • v
  have hy_norm : ‖y‖ = 1 := by
    -- The normalization has unit norm because `v` is nonzero.
    calc
      ‖y‖ = |‖v‖⁻¹| * ‖v‖ := by
        simpa [y] using (norm_smul (‖v‖⁻¹) v)
      _ = 1 := by
        rw [abs_inv, abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ (norm_ne_zero_iff.2 hv)]
  have hv_eq : v = ‖v‖ • y := by
    -- Recover `v` by scaling its normalization back by its norm.
    calc
      v = (‖v‖ * ‖v‖⁻¹) • v := by
        rw [mul_inv_cancel₀ (norm_ne_zero_iff.2 hv), one_smul]
      _ = ‖v‖ • y := by
        simp [y, smul_smul]
  have hcol : v - y = (‖v‖ - 1) • y := by
    -- The vector `v - y` stays on the same line as `y`.
    calc
      v - y = ‖v‖ • y - y := by
        simpa using congrArg (fun z => z - y) hv_eq
      _ = ‖v‖ • y - 1 • y := by rw [one_smul]
      _ = (‖v‖ - 1) • y := by
        simpa using (sub_smul ‖v‖ (1 : ℝ) y).symm
  have hvy : ‖v - y‖ = |‖v‖ - 1| := by
    -- Since `v` and `y` are positively collinear, their distance is the norm defect.
    calc
      ‖v - y‖ = ‖(‖v‖ - 1) • y‖ := by
        rw [hcol]
      _ = |‖v‖ - 1| * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = |‖v‖ - 1| := by simp [hy_norm]
  have hnorm_defect : |‖v‖ - 1| ≤ ‖x - v‖ := by
    -- The reverse triangle inequality controls the norm defect by the ambient distance.
    calc
      |‖v‖ - 1| ≤ ‖v - x‖ := by simpa [hx] using abs_norm_sub_norm_le v x
      _ = ‖x - v‖ := by rw [norm_sub_rev]
  calc
    ‖x - y‖ ≤ ‖x - v‖ + ‖v - y‖ := by
      -- Split the error into the truncation part and the normalization part.
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (norm_add_le (x - v) (v - y))
    _ = ‖x - v‖ + |‖v‖ - 1| := by rw [hvy]
    _ ≤ ‖x - v‖ + ‖x - v‖ := by gcongr
    _ = 2 * ‖x - v‖ := by ring

/-- Helper for Proposition 2.49: a finite stage of the asymptotic orthonormal subsequence
construction records a finite subsequence, an orthonormal comparison family, and the stagewise
approximation bounds. -/
private structure AlmostOrthonormalState (x : ℕ → H) (ε : ℕ → ℝ) (n : ℕ) where
  /-- The finite extraction map at stage `n`. -/
  k : Fin (n + 1) → ℕ
  /-- The finite orthonormal comparison family at stage `n`. -/
  y : Fin (n + 1) → H
  /-- The finite extraction map is strictly monotone. -/
  strictMono_k : StrictMono k
  /-- The finite comparison family is orthonormal. -/
  orthonormal_y : Orthonormal ℝ y
  /-- Each extracted vector is close to its comparison vector. -/
  close : ∀ i, ‖x (k i) - y i‖ ≤ ε i

omit [CompleteSpace H] in
/-- Helper for Proposition 2.49: the finite linear combination built from the inner products
against an orthonormal family has norm controlled by the sum of the coefficient bounds. -/
-- Proof sketch: estimate the norm of the sum by the sum of the norms and then use the unit norm of
-- each orthonormal vector.
private lemma norm_sum_inner_smul_le {n : ℕ} {y : Fin (n + 1) → H} (hy : Orthonormal ℝ y) (z : H)
    {δ : ℝ} (hsmall : ∀ i, |inner ℝ (y i) z| ≤ δ) :
    ‖∑ i : Fin (n + 1), inner ℝ (y i) z • y i‖ ≤ (n + 1 : ℝ) * δ := by
  have hterm : ∀ i : Fin (n + 1), ‖inner ℝ (y i) z • y i‖ = |inner ℝ (y i) z| := by
    intro i
    rw [norm_smul, hy.norm_eq_one i, mul_one, Real.norm_eq_abs]
  calc
    ‖∑ i : Fin (n + 1), inner ℝ (y i) z • y i‖ ≤
        ∑ i : Fin (n + 1), ‖inner ℝ (y i) z • y i‖ := by
      exact norm_sum_le _ _
    _ = ∑ i : Fin (n + 1), |inner ℝ (y i) z| := by
      simp [hterm]
    _ ≤ ∑ i : Fin (n + 1), δ := by
      exact Finset.sum_le_sum fun i _ ↦ hsmall i
    _ = (n + 1 : ℝ) * δ := by
      simp [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

omit [CompleteSpace H] in
/-- Helper for Proposition 2.49: subtracting the finite inner-product expansion makes the residual
orthogonal to each member of the orthonormal family. -/
-- Proof sketch: the orthonormal expansion reproduces the chosen coordinate, so the coordinate of
-- the residual vanishes after subtraction.
private lemma inner_residual_eq_zero {n : ℕ} {y : Fin (n + 1) → H} (hy : Orthonormal ℝ y) (z : H)
    (i : Fin (n + 1)) :
    inner ℝ (y i) (z - ∑ j : Fin (n + 1), inner ℝ (y j) z • y j) = 0 := by
  rw [inner_sub_right, hy.inner_right_fintype, sub_self]

omit [CompleteSpace H] in
/-- Helper for Proposition 2.49: adjoining the normalized residual of an orthonormal finite family
preserves orthonormality when the residual is orthogonal to the old family and nonzero. -/
-- Proof sketch: old-old pairs stay orthonormal, old-new and new-old pairs vanish by the residual
-- orthogonality, and the normalized residual has norm one.
private lemma orthonormal_snoc_normalized {n : ℕ} {y : Fin (n + 1) → H} (hy : Orthonormal ℝ y)
    {v : H}
    (hv : ∀ i, inner ℝ (y i) v = 0) (hv_ne : v ≠ 0) :
    Orthonormal ℝ (Fin.snoc y ((‖v‖)⁻¹ • v)) := by
  constructor
  · intro i
    cases i using Fin.lastCases with
    | last =>
        -- The new vector is normalized by the inverse of its norm.
        have hnorm : ‖(‖v‖)⁻¹ • v‖ = 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
            inv_mul_cancel₀ (norm_ne_zero_iff.2 hv_ne)]
        simpa [Fin.snoc_last] using hnorm
    | cast i =>
        -- The old entries keep their unit norm.
        simpa using hy.norm_eq_one i
  · intro i j hij
    cases i using Fin.lastCases with
    | last =>
        cases j using Fin.lastCases with
        | last =>
            exact (hij rfl).elim
        | cast j =>
            -- The new vector is orthogonal to every old entry by assumption.
            have hv' : inner ℝ v (y j) = 0 := by
              simpa [real_inner_comm] using hv j
            simp [Fin.snoc_last, Fin.snoc_castSucc, hv', inner_smul_left]
    | cast i =>
        cases j using Fin.lastCases with
        | last =>
            -- The old vector is orthogonal to the new residual.
            simp [Fin.snoc_last, Fin.snoc_castSucc, hv i, inner_smul_right]
        | cast j =>
            -- Old-old pairs inherit orthogonality from the previous stage.
            have hneq : i ≠ j := by
              intro hij'
              apply hij
              simp [hij']
            simpa [Fin.snoc_castSucc] using hy.inner_eq_zero hneq

/-- Helper for Proposition 2.49: one finite almost-orthonormal stage can be extended by choosing a
later vector that is nearly orthogonal to the old family and normalizing its residual. -/
-- Proof sketch: choose a far index with uniformly small inner products against the old orthonormal
-- family, subtract the finite orthogonal expansion, normalize the residual, and append the new
-- data by `Fin.snoc`.
private lemma extend_almost_orthonormal_state (x : ℕ → H)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (nhds (0 : WeakSpace ℝ H)))
    (hx_norm : ∀ n : ℕ, ‖x n‖ = 1) {ε : ℕ → ℝ} {n : ℕ}
    (s : AlmostOrthonormalState x ε n) (hε_pos : 0 < ε (n + 1)) (hε_small : ε (n + 1) < 1 / 2) :
    ∃ s' : AlmostOrthonormalState x ε (n + 1),
      (∀ i : Fin (n + 1), s'.k i.castSucc = s.k i) ∧
      (∀ i : Fin (n + 1), s'.y i.castSucc = s.y i) := by
  let δ : ℝ := ε (n + 1) / (2 * (n + 1 : ℝ))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  rcases exists_far_index_with_small_inner_family x hx s.y (s.k (Fin.last n)) hδ_pos with
    ⟨m, hm_gt, hm_small⟩
  let p : H := ∑ i : Fin (n + 1), inner ℝ (s.y i) (x m) • s.y i
  let v : H := x m - p
  let yNew : H := (‖v‖)⁻¹ • v
  have hp_norm_le : ‖p‖ ≤ (n + 1 : ℝ) * δ := by
    -- The old coordinates are all small, so the finite orthogonal expansion is small as well.
    exact norm_sum_inner_smul_le s.orthonormal_y (x m) fun i ↦
      le_of_lt (hm_small i)
  have hp_half : ‖p‖ ≤ ε (n + 1) / 2 := by
    -- The chosen threshold makes the whole projection error at most `ε (n+1) / 2`.
    have hcard_pos : (0 : ℝ) < n + 1 := by positivity
    have hδ_mul : (n + 1 : ℝ) * δ = ε (n + 1) / 2 := by
      dsimp [δ]
      field_simp [hcard_pos.ne']
    calc
      ‖p‖ ≤ (n + 1 : ℝ) * δ := hp_norm_le
      _ = ε (n + 1) / 2 := hδ_mul
  have hxv : x m - v = p := by
    -- By construction, `v` is the residual after removing the finite orthogonal expansion.
    simp [v, p, sub_eq_add_neg, add_comm]
  have hv_dist : ‖x m - v‖ ≤ ε (n + 1) / 2 := by
    simpa [hxv] using hp_half
  have hv_ne : v ≠ 0 := by
    -- If the residual vanished, the unit vector `x m` would lie too close to `0`.
    intro hv_zero
    have hhalf_lt_one : ε (n + 1) / 2 < 1 := by
      nlinarith
    have : (1 : ℝ) ≤ ε (n + 1) / 2 := by
      calc
        (1 : ℝ) = ‖x m‖ := by simp [hx_norm m]
        _ = ‖x m - v‖ := by simp [hv_zero]
        _ ≤ ε (n + 1) / 2 := hv_dist
    linarith
  refine ⟨
    { k := Fin.snoc s.k m
      y := Fin.snoc s.y yNew
      strictMono_k := ?_
      orthonormal_y := ?_
      close := ?_ },
    ?_,
    ?_⟩
  · -- Appending a strictly later index preserves the strict monotonicity of the extraction map.
    intro i j hij
    cases j using Fin.lastCases with
    | last =>
        cases i using Fin.lastCases with
        | last =>
            exact (lt_irrefl _ hij).elim
        | cast i =>
            have hi_le : s.k i ≤ s.k (Fin.last n) := by
              by_cases hi_last : i = Fin.last n
              · simp [hi_last]
              · exact le_of_lt (s.strictMono_k (lt_of_le_of_ne (Fin.le_last i) hi_last))
            simpa [Fin.snoc_castSucc, Fin.snoc_last] using lt_of_le_of_lt hi_le hm_gt
    | cast j =>
        cases i using Fin.lastCases with
        | last =>
            exact (not_lt_of_ge (Fin.le_last _)) hij |>.elim
        | cast i =>
            simpa [Fin.snoc_castSucc] using s.strictMono_k (Fin.castSucc_lt_castSucc_iff.1 hij)
  · -- The new comparison vector is the normalized residual, hence orthonormal to the old family.
    apply orthonormal_snoc_normalized s.orthonormal_y
    · intro i
      simpa [v, p] using inner_residual_eq_zero s.orthonormal_y (x m) i
    · exact hv_ne
  · intro i
    cases i using Fin.lastCases with
    | last =>
        -- The last error estimate comes from the residual approximation and the normalization bound.
        have hnormalize :
            ‖x m - yNew‖ ≤ 2 * ‖x m - v‖ := by
          simpa [yNew] using
            norm_sub_normalized_block_le_twice (hx_norm m) hv_ne
        simpa [Fin.snoc_last] using
          (calc
            ‖x m - yNew‖ ≤ 2 * ‖x m - v‖ := hnormalize
            _ ≤ 2 * (ε (n + 1) / 2) := by gcongr
            _ = ε (n + 1) := by ring)
    | cast i =>
        -- The old error bounds are preserved on the old coordinates.
        simpa [Fin.snoc_castSucc] using s.close i
  · intro i
    simp [Fin.snoc_castSucc]
  · intro i
    simp [Fin.snoc_castSucc]

/-- Proposition 2.49: a weakly null sequence of unit vectors in a real Hilbert space admits a
subsequence that is asymptotic in norm to an orthonormal sequence. -/
-- Proof sketch: choose a Hilbert basis of the closed span of the sequence and inductively extract
-- a subsequence whose low-frequency and high-frequency Fourier tails are both small on successive
-- disjoint blocks. The block truncations form an orthogonal sequence; normalizing them gives an
-- orthonormal sequence, and the truncation error tends to `0`.
theorem exists_subseq_tendsto_zero_sub_orthonormal_of_tendsto_zero_weakly_of_norm_eq_one
    (x : ℕ → H)
    (hx : Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (nhds (0 : WeakSpace ℝ H)))
    (hx_norm : ∀ n : ℕ, ‖x n‖ = 1) :
    ∃ subseq : ℕ → ℕ, ∃ orthonormalSeq : ℕ → H,
      StrictMono subseq ∧
        Orthonormal ℝ orthonormalSeq ∧
          Tendsto (fun n ↦ x (subseq n) - orthonormalSeq n) atTop (nhds (0 : H)) := by
  classical
  let ε : ℕ → ℝ := fun n ↦ ((n : ℝ) + 4)⁻¹
  have hε_pos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    positivity
  have hε_small : ∀ n, ε n < 1 / 2 := by
    intro n
    have hn : (0 : ℝ) ≤ n := by
      exact_mod_cast Nat.zero_le n
    have htwo : (2 : ℝ) < (n : ℝ) + 4 := by
      nlinarith
    simpa [ε] using one_div_lt_one_div_of_lt (show (0 : ℝ) < 2 by norm_num) htwo
  have hbase : AlmostOrthonormalState x ε 0 := by
    refine
      { k := fun _ ↦ 0
        y := fun _ ↦ x 0
        strictMono_k := ?_
        orthonormal_y := ?_
        close := ?_ }
    · intro i j hij
      fin_cases i
      fin_cases j
      exact (lt_irrefl _ hij).elim
    · -- The first stage consists of the singleton unit vector `x 0`.
      rw [orthonormal_iff_ite]
      intro i j
      fin_cases i
      fin_cases j
      simp [hx_norm 0]
    · -- The singleton stage has zero approximation error.
      intro i
      fin_cases i
      simpa [ε] using (show (0 : ℝ) ≤ ε 0 from le_of_lt (hε_pos 0))
  let states : ∀ n, AlmostOrthonormalState x ε n :=
    fun n ↦
      Nat.rec hbase
        (fun n s ↦
          Classical.choose <|
            extend_almost_orthonormal_state x hx hx_norm s (hε_pos (n + 1))
              (hε_small (n + 1)))
        n
  have hstates_prefix :
      ∀ n,
        (∀ i : Fin (n + 1), (states (n + 1)).k i.castSucc = (states n).k i) ∧
        (∀ i : Fin (n + 1), (states (n + 1)).y i.castSucc = (states n).y i) := by
    intro n
    simpa [states] using
      (Classical.choose_spec <|
        extend_almost_orthonormal_state x hx hx_norm (states n) (hε_pos (n + 1))
          (hε_small (n + 1)))
  let subseq : ℕ → ℕ := fun n ↦ (states n).k (Fin.last n)
  let orthSeq : ℕ → H := fun n ↦ (states n).y (Fin.last n)
  have hstate_value :
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (states n).y ⟨m, Nat.lt_succ_of_le hmn⟩ = orthSeq m := by
    intro m n hmn
    induction n with
    | zero =>
        have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
        subst hm
        simp [orthSeq]
    | succ n ihn =>
        by_cases hmn_eq : m = n + 1
        · subst hmn_eq
          have hlast :
              (⟨n + 1, Nat.lt_succ_of_le hmn⟩ : Fin (n + 2)) = Fin.last (n + 1) := by
            ext
            rfl
          simp [orthSeq, hlast]
        · have hmn' : m ≤ n := by
            exact Nat.le_of_lt_succ (lt_of_le_of_ne hmn hmn_eq)
          have hpref := (hstates_prefix n).2
          calc
            (states (n + 1)).y ⟨m, Nat.lt_succ_of_le hmn⟩
                = (states n).y ⟨m, Nat.lt_succ_of_le hmn'⟩ := by
                    have hindex :
                        (⟨m, Nat.lt_succ_of_le hmn⟩ : Fin (n + 2)) =
                          (⟨m, Nat.lt_succ_of_le hmn'⟩ : Fin (n + 1)).castSucc := by
                      ext
                      rfl
                    rw [hindex]
                    exact hpref _
            _ = orthSeq m := ihn hmn'
  have hsubseq_strict : StrictMono subseq := by
    refine strictMono_nat_of_lt_succ fun n ↦ ?_
    have hlast :
        (states (n + 1)).k (Fin.castSucc (Fin.last n)) < (states (n + 1)).k (Fin.last (n + 1)) :=
      (states (n + 1)).strictMono_k (by simpa using (Fin.castSucc_lt_last (Fin.last n)))
    simpa [subseq, (hstates_prefix n).1 (Fin.last n)] using hlast
  have horthSeq : Orthonormal ℝ orthSeq := by
    constructor
    · intro n
      simpa [orthSeq] using (states n).orthonormal_y.norm_eq_one (Fin.last n)
    · intro i j hij
      rcases lt_or_gt_of_ne hij with hij_lt | hij_gt
      · have hi_state :
            orthSeq i = (states j).y ⟨i, Nat.lt_succ_of_lt hij_lt⟩ := by
          symm
          exact hstate_value (Nat.le_of_lt hij_lt)
        calc
          inner ℝ (orthSeq i) (orthSeq j)
              = inner ℝ ((states j).y ⟨i, Nat.lt_succ_of_lt hij_lt⟩)
                  ((states j).y (Fin.last j)) := by
                    simp [orthSeq, hi_state]
          _ = 0 := by
            apply (states j).orthonormal_y.inner_eq_zero
            exact Fin.ne_of_lt (by simpa using hij_lt)
      · have hj_state :
            orthSeq j = (states i).y ⟨j, Nat.lt_succ_of_lt hij_gt⟩ := by
          symm
          exact hstate_value (Nat.le_of_lt hij_gt)
        calc
          inner ℝ (orthSeq i) (orthSeq j)
              = inner ℝ (orthSeq j) (orthSeq i) := by rw [real_inner_comm]
          _ = inner ℝ ((states i).y ⟨j, Nat.lt_succ_of_lt hij_gt⟩)
                ((states i).y (Fin.last i)) := by
                  simp [orthSeq, hj_state]
          _ = 0 := by
            apply (states i).orthonormal_y.inner_eq_zero
            exact Fin.ne_of_lt (by simpa using hij_gt)
  have hclose : ∀ n, ‖x (subseq n) - orthSeq n‖ ≤ ε n := by
    intro n
    simpa [subseq, orthSeq] using (states n).close (Fin.last n)
  have hε_tendsto : Tendsto ε atTop (nhds 0) := by
    have hshift : Tendsto (fun n : ℕ ↦ (n : ℝ) + 4) atTop atTop :=
      tendsto_atTop_add_const_right atTop 4 tendsto_natCast_atTop_atTop
    simpa [ε] using tendsto_inv_atTop_zero.comp hshift
  refine ⟨subseq, orthSeq, hsubseq_strict, horthSeq, ?_⟩
  -- The stagewise error bounds are dominated by the explicit sequence `ε n → 0`.
  exact squeeze_zero_norm hclose hε_tendsto

/-! Source item: Chap02/Proposition_2_50 -/


/-- Helper for Proposition 2.50: a weak sequential cluster point supplies a subsequence whose
inner-product coordinates converge against every fixed vector. -/
private lemma subsequence_inner_tendsto_of_weak_cluster_point
    {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    {xₙ : ℕ → 𝓗} {y : 𝓗}
    (hy : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ 𝓗 (xₙ n)) (toWeakSpace ℝ 𝓗 y)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ v : 𝓗, Tendsto (fun n ↦ inner ℝ (xₙ (φ n)) v) atTop (𝓝 (inner ℝ y v)) := by
  rcases hy with ⟨φ, hφ, hφ_tendsto⟩
  refine ⟨φ, hφ, ?_⟩
  intro v
  -- Compose the weakly convergent subsequence with the continuous coordinate functional.
  simpa using
    (weakSpace_continuous_inner_right v).tendsto (toWeakSpace ℝ 𝓗 y) |>.comp hφ_tendsto

/-- Helper for Proposition 2.50: if `y - x` has zero inner product against every generator of a
dense family, then `y - x` lies in the orthogonal complement of the generated span. -/
private lemma sub_mem_orthogonal_span_of_inner_eq_zero
    {I : Type v} {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
    (e : I → 𝓗) {x y : 𝓗}
    (hinner : ∀ i : I, inner ℝ (y - x) (e i) = 0) :
    y - x ∈ (Submodule.span ℝ (Set.range e))ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro u hu
  -- Extend the vanishing from the generators to the whole span by linearity in the second slot.
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
  · intro u hu
    rcases hu with ⟨i, rfl⟩
    exact hinner i
  · simp
  · intro u v _ _ hu hv
    simp [inner_add_right, hu, hv]
  · intro a u _ hu
    simp [inner_smul_right, hu]

/-- Helper for Proposition 2.50: dense-span coordinate agreement forces a weak sequential cluster
point to equal the target vector. -/
private lemma weak_cluster_point_eq_target_of_dense_span
    {I : Type v} {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    (e : I → 𝓗)
    (h_dense : Dense ((Submodule.span ℝ (Set.range e) : Set 𝓗)))
    {xₙ : ℕ → 𝓗} {x y : 𝓗}
    (hcoord : ∀ i : I,
      Tendsto (fun n ↦ inner ℝ (xₙ n) (e i)) atTop (𝓝 (inner ℝ x (e i))))
    (hy : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ 𝓗 (xₙ n)) (toWeakSpace ℝ 𝓗 y)) :
    y = x := by
  rcases subsequence_inner_tendsto_of_weak_cluster_point hy with ⟨φ, hφ, hφ_inner⟩
  have h_eq_coords : ∀ i : I, inner ℝ y (e i) = inner ℝ x (e i) := by
    intro i
    -- The same subsequence converges to both coordinate values, so the limits agree.
    have hsubseq_x :
        Tendsto (fun n ↦ inner ℝ (xₙ (φ n)) (e i)) atTop (𝓝 (inner ℝ x (e i))) :=
      (hcoord i).comp hφ.tendsto_atTop
    exact tendsto_nhds_unique (hφ_inner (e i)) hsubseq_x
  have hsub_mem : y - x ∈ (Submodule.span ℝ (Set.range e))ᗮ := by
    -- Route correction: move from coordinate equalities to orthogonality of `y - x`.
    apply sub_mem_orthogonal_span_of_inner_eq_zero e
    intro i
    rw [inner_sub_left, h_eq_coords i, sub_self]
  exact h_dense.eq_of_sub_mem_orthogonal hsub_mem

/-- Proposition 2.50: for a sequence in a real Hilbert space, weak convergence to `x` is
equivalent to norm-boundedness together with convergence of the inner-product coordinates against
every vector in a family whose linear span is dense. -/
-- Proof sketch: the forward implication follows because weak convergence gives convergence of every
-- continuous coordinate functional, and boundedness follows from the standard boundedness criterion
-- for weakly convergent sequences. For the converse, apply the weak compactness subsequence
-- criterion to the bounded sequence `xₙ - x`; every weak sequential cluster point is orthogonal to
-- the dense spanning family, hence zero, so the sequence has a unique weak cluster point and
-- therefore converges weakly to `x`.
theorem tendsto_weakly_iff_bounded_and_inner_tendsto_of_dense_span
    {I : Type v} {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
    (e : I → 𝓗)
    (h_dense : Dense ((Submodule.span ℝ (Set.range e) : Set 𝓗)))
    (xₙ : ℕ → 𝓗) (x : 𝓗) :
    Tendsto (fun n ↦ toWeakSpace ℝ 𝓗 (xₙ n)) atTop (𝓝 (toWeakSpace ℝ 𝓗 x)) ↔
      Bornology.IsBounded (Set.range xₙ) ∧
        ∀ i : I,
          Tendsto (fun n ↦ inner ℝ (xₙ n) (e i)) atTop (𝓝 (inner ℝ x (e i))) := by
  constructor
  · intro hx
    refine ⟨bounded_range_of_tendsto_weakly hx, ?_⟩
    intro i
    -- Weak convergence transports through each continuous coordinate functional.
    simpa using
      (weakSpace_continuous_inner_right (e i)).tendsto (toWeakSpace ℝ 𝓗 x) |>.comp hx
  · rintro ⟨hx_bounded, hcoord⟩
    -- Apply the weak compactness criterion once dense-span uniqueness of cluster points is proved.
    have huniq :
        ∀ y z : 𝓗,
          IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ 𝓗 (xₙ n)) (toWeakSpace ℝ 𝓗 y) →
          IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ 𝓗 (xₙ n)) (toWeakSpace ℝ 𝓗 z) →
          y = z := by
      intro y z hy hz
      calc
        y = x := weak_cluster_point_eq_target_of_dense_span e h_dense hcoord hy
        _ = z := (weak_cluster_point_eq_target_of_dense_span e h_dense hcoord hz).symm
    rcases
        (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint xₙ).2
          ⟨hx_bounded, huniq⟩ with
      ⟨y, hy⟩
    have hy_cluster :
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ 𝓗 (xₙ n)) (toWeakSpace ℝ 𝓗 y) := by
      exact ⟨id, strictMono_id, by simpa using hy⟩
    have hy_eq : y = x := weak_cluster_point_eq_target_of_dense_span e h_dense hcoord hy_cluster
    simpa [hy_eq] using hy

/-! Source item: Chap02/Corollary_2_52 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

-- Proof sketch: strong convergence implies weak convergence by continuity of the canonical map to
-- `WeakSpace ℝ 𝓗`, and it implies norm convergence by continuity of the norm. Conversely, test the
-- weak convergence against the fixed coordinate `y ↦ ⟪y, x⟫`, expand `‖xₙ - x‖²`, and use the
-- convergence of the norms to show the squared distances tend to `0`.
/-- Corollary 2.52: a sequence in a Hilbert space converges strongly to `x` if and only if it
converges weakly to `x` in the canonical weak topology `WeakSpace ℝ 𝓗` and its norms converge to
`‖x‖`. -/
theorem tendsto_iff_tendsto_weakly_and_tendsto_norm (xₙ : ℕ → 𝓗) (x : 𝓗) :
    Tendsto xₙ atTop (𝓝 x) ↔
      Tendsto (fun n ↦ toWeakSpace ℝ 𝓗 (xₙ n)) atTop (𝓝 (toWeakSpace ℝ 𝓗 x)) ∧
        Tendsto (fun n ↦ ‖xₙ n‖) atTop (𝓝 ‖x‖) := by
  constructor
  · intro hx
    constructor
    -- Send the strong limit through the canonical continuous map to the weak space.
    · simpa [toWeakSpaceCLM_eq_toWeakSpace] using
        ((toWeakSpaceCLM ℝ 𝓗).continuous.tendsto x).comp hx
    -- Apply continuity of the norm to get convergence of the norm sequence.
    · simpa using (continuous_norm.tendsto x).comp hx
  · intro h
    rcases h with ⟨hWeak, hNorm⟩
    -- Recover strong convergence by showing that the squared norms of `xₙ - x` tend to `0`.
    rw [tendsto_iff_norm_sub_tendsto_zero]
    -- Weak convergence gives convergence of the fixed-coordinate functional `y ↦ ⟪x, y⟫`.
    have hInner : Tendsto (fun n ↦ inner ℝ x (xₙ n)) atTop (𝓝 (‖x‖ ^ 2)) := by
      have hEval :
          Tendsto
            (fun n ↦
              ((topDualPairing ℝ 𝓗).flip (toWeakSpace ℝ 𝓗 (xₙ n))
                (InnerProductSpace.toDual ℝ 𝓗 x)))
            atTop
            (𝓝
              ((topDualPairing ℝ 𝓗).flip (toWeakSpace ℝ 𝓗 x)
                (InnerProductSpace.toDual ℝ 𝓗 x))) := by
        exact
          ((WeakBilin.eval_continuous ((topDualPairing ℝ 𝓗).flip)
              (InnerProductSpace.toDual ℝ 𝓗 x)).tendsto (toWeakSpace ℝ 𝓗 x)).comp hWeak
      change Tendsto (fun n ↦ inner ℝ x (xₙ n)) atTop (𝓝 (inner ℝ x x)) at hEval
      simpa [real_inner_self_eq_norm_sq] using hEval
    have hNormSq : Tendsto (fun n ↦ ‖xₙ n‖ ^ 2) atTop (𝓝 (‖x‖ ^ 2)) := by
      simpa using hNorm.pow 2
    have hSqDiffEq :
        (fun n ↦ ‖xₙ n - x‖ ^ 2) =
          (fun n ↦ ‖xₙ n‖ ^ 2 - 2 * inner ℝ x (xₙ n) + ‖x‖ ^ 2) := by
      funext n
      calc
        ‖xₙ n - x‖ ^ 2 = inner ℝ (xₙ n - x) (xₙ n - x) := by
          rw [real_inner_self_eq_norm_sq]
        _ = inner ℝ (xₙ n) (xₙ n) - inner ℝ (xₙ n) x - inner ℝ x (xₙ n) + inner ℝ x x := by
          rw [inner_sub_right, inner_sub_left, inner_sub_left]
          ring
        _ = ‖xₙ n‖ ^ 2 - 2 * inner ℝ x (xₙ n) + ‖x‖ ^ 2 := by
          rw [real_inner_comm (xₙ n) x, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
          ring
    have hSqDiff : Tendsto (fun n ↦ ‖xₙ n - x‖ ^ 2) atTop (𝓝 0) := by
      rw [hSqDiffEq]
      -- The polarization identity shows that all terms converge to cancel at `0`.
      have hTwoInner :
          Tendsto (fun n ↦ 2 * inner ℝ x (xₙ n)) atTop (𝓝 (2 * (‖x‖ ^ 2))) := by
        exact hInner.const_mul 2
      have hConst : Tendsto (fun _ : ℕ ↦ ‖x‖ ^ 2) atTop (𝓝 (‖x‖ ^ 2)) :=
        tendsto_const_nhds
      have hSum :
          Tendsto (fun n ↦ ‖xₙ n‖ ^ 2 - 2 * inner ℝ x (xₙ n) + ‖x‖ ^ 2)
            atTop (𝓝 (‖x‖ ^ 2 - 2 * (‖x‖ ^ 2) + ‖x‖ ^ 2)) := by
        exact (hNormSq.sub hTwoInner).add hConst
      have hLimitZero : (‖x‖ ^ 2 - 2 * (‖x‖ ^ 2) + ‖x‖ ^ 2 : ℝ) = 0 := by
        ring
      simpa [hLimitZero] using hSum
    have hNormSub : Tendsto (fun n ↦ ‖xₙ n - x‖) atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hSqEventually : ∀ᶠ n in atTop, dist (‖xₙ n - x‖ ^ 2) 0 < ε ^ 2 := by
        exact (Metric.tendsto_nhds.1 hSqDiff) (ε ^ 2) (sq_pos_of_pos hε)
      filter_upwards [hSqEventually] with n hn
      have hsquare_lt : ‖xₙ n - x‖ ^ 2 < ε ^ 2 := by
        simpa [Real.dist_eq, abs_of_nonneg (sq_nonneg ‖xₙ n - x‖)] using hn
      -- Since norms are nonnegative, controlling the square controls the norm itself.
      simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg (xₙ n - x))] using
        (sq_lt_sq₀ (norm_nonneg (xₙ n - x)) hε.le).1 hsquare_lt
    exact hNormSub

/-! Source item: Chap02/Lemma_2_53 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
  [FiniteDimensional ℝ 𝓗]

-- Proof sketch: in finite dimension, the closure of a bounded set is compact. The cluster-point
-- set is closed, hence compact inside that closure, and `Theorem_1_49` gives connectedness from
-- the vanishing successive increments.
/-- Lemma 2.53: for a bounded sequence in a finite-dimensional Hilbert space whose successive
increments converge to `0`, the set of its cluster points, expressed via the canonical filter-based
notion `MapClusterPt`, is compact and connected. -/
theorem sequenceClusterPointSet_isCompact_isConnected (x : ℕ → 𝓗)
    (hbounded : Bornology.IsBounded (Set.range x))
    (hstep : Tendsto (fun n ↦ x n - x (n + 1)) atTop (𝓝 0)) :
    IsCompact {y | MapClusterPt y atTop x} ∧ IsConnected {y | MapClusterPt y atTop x} := by
  let K : Set 𝓗 := closure (Set.range x)
  haveI : ProperSpace 𝓗 := FiniteDimensional.proper ℝ 𝓗
  have hKcompact : IsCompact K := by
    simpa [K] using hbounded.isCompact_closure
  have hseq_in_K : ∀ n, x n ∈ K := fun n ↦ subset_closure ⟨n, rfl⟩
  have hclosed : IsClosed {y | MapClusterPt y atTop x} := by
    simpa [MapClusterPt] using
      (isClosed_setOf_clusterPt : IsClosed {y | ClusterPt y (map x atTop)})
  have hsubset : {y | MapClusterPt y atTop x} ⊆ K := by
    intro y hy
    exact IsClosed.mem_of_mapClusterPt isClosed_closure hy
      (Filter.Eventually.of_forall fun n ↦ subset_closure ⟨n, rfl⟩)
  have hcompact : IsCompact {y | MapClusterPt y atTop x} :=
    hKcompact.of_isClosed_subset hclosed hsubset
  have hconnected : IsConnected {y | MapClusterPt y atTop x} := by
    refine isConnected_clusterPoints_of_tendsto_dist_succ_eq_zero hKcompact hseq_in_K ?_
    simpa [dist_eq_norm] using hstep.norm
  exact ⟨hcompact, hconnected⟩

/-! Source item: Chap03/Example_3_33 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Helper for Example 3.33: distinct weighted orthonormal vectors satisfy the Pythagorean
distance identity. -/
private lemma scaled_orthonormal_dist_sq_eq_of_ne (e : ℕ → 𝓗) (he : Orthonormal ℝ e) (α : ℕ → ℝ)
    (hα_ge_one : ∀ n : ℕ, 1 ≤ α n) {m n : ℕ} (hmn : m ≠ n) :
    ‖α m • e m - α n • e n‖ ^ 2 = α m ^ 2 + α n ^ 2 := by
  -- Positivity of the weights removes the absolute values in the norm computations.
  have hαm_nonneg : 0 ≤ α m := le_trans zero_le_one (hα_ge_one m)
  have hαn_nonneg : 0 ≤ α n := le_trans zero_le_one (hα_ge_one n)
  have hm : ‖α m • e m‖ = α m := by
    rw [norm_smul, he.norm_eq_one m, mul_one, Real.norm_of_nonneg hαm_nonneg]
  have hn : ‖α n • e n‖ = α n := by
    rw [norm_smul, he.norm_eq_one n, mul_one, Real.norm_of_nonneg hαn_nonneg]
  have hinner : inner ℝ (α m • e m) (α n • e n) = 0 := by
    rw [real_inner_smul_left, inner_smul_right, he.inner_eq_zero hmn, mul_zero, mul_zero]
  -- Then the real inner-product norm expansion collapses to a sum of squares.
  rw [norm_sub_sq_real, hm, hn, hinner]
  ring

/-- Helper for Example 3.33: distinct weighted orthonormal vectors stay more than unit distance
apart. -/
private lemma scaled_orthonormal_dist_gt_one_of_ne (e : ℕ → 𝓗) (he : Orthonormal ℝ e)
    (α : ℕ → ℝ)
    (hα_ge_one : ∀ n : ℕ, 1 ≤ α n) {m n : ℕ} (hmn : m ≠ n) :
    1 < dist (α m • e m) (α n • e n) := by
  -- The squared distance is at least `2`, so the distance is strictly larger than `1`.
  have hsq :
      dist (α m • e m) (α n • e n) ^ 2 = α m ^ 2 + α n ^ 2 := by
    simpa [dist_eq_norm] using
      scaled_orthonormal_dist_sq_eq_of_ne e he α hα_ge_one hmn
  have hnonneg : 0 ≤ dist (α m • e m) (α n • e n) := dist_nonneg
  nlinarith [hsq, hα_ge_one m, hα_ge_one n]

/-- Helper for Example 3.33: every norm-convergent sequence in the weighted orthonormal range is
eventually constant. -/
private lemma eventually_constant_of_tendsto_scaled_orthonormal_range (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e)
    (α : ℕ → ℝ) (hα_ge_one : ∀ n : ℕ, 1 ≤ α n) {u : ℕ → 𝓗} {x : 𝓗}
    (hu : ∀ n : ℕ, u n ∈ Set.range (fun k ↦ α k • e k)) (hx : Tendsto u atTop (𝓝 x)) :
    ∃ N k, ∀ n ≥ N, u n = α k • e k := by
  -- Convergent sequences are Cauchy, so eventually every later term lies within distance `< 1`
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
    exact scaled_orthonormal_dist_gt_one_of_ne e he α hα_ge_one hkne
  linarith

/-- Helper for Example 3.33: the weighted orthonormal range is norm closed once distinct points are
uniformly separated. -/
private theorem isClosed_scaled_orthonormal_range (e : ℕ → 𝓗) (he : Orthonormal ℝ e)
    (α : ℕ → ℝ) (hα_ge_one : ∀ n : ℕ, 1 ≤ α n) :
    IsClosed (Set.range (fun n ↦ α n • e n)) := by
  have hseqClosed : IsSeqClosed (Set.range (fun n ↦ α n • e n)) := by
    intro u x hu hx
    rcases eventually_constant_of_tendsto_scaled_orthonormal_range e he α hα_ge_one hu hx with
      ⟨N, k, hNk⟩
    have hconst : u =ᶠ[atTop] fun _ ↦ α k • e k := by
      exact Filter.eventually_atTop.2 ⟨N, fun n hn ↦ hNk n hn⟩
    have hxconst : Tendsto (fun _ : ℕ ↦ α k • e k) atTop (𝓝 x) := hx.congr' hconst
    have hxeq : x = α k • e k := tendsto_nhds_unique hxconst tendsto_const_nhds
    exact Set.mem_range.2 ⟨k, hxeq.symm⟩
  exact isSeqClosed_iff_isClosed.1 hseqClosed

variable [CompleteSpace 𝓗]

omit [CompleteSpace 𝓗] in
/-- Helper for Example 3.33: bounded weighted orthonormal values admit a constant subsequence of
their indices once the weights tend to `+∞`. -/
private lemma exists_constant_subseq_of_bounded_scaled_orthonormal_values (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) (α : ℕ → ℝ) (hα_tendsto : Tendsto α atTop atTop) {n : ℕ → ℕ}
    (hbounded : Bornology.IsBounded (Set.range fun k ↦ α (n k) • e (n k))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ j : ℕ, ∀ k, n (φ k) = j := by
  rcases isBounded_iff_forall_norm_le.mp hbounded with ⟨C₀, hC₀⟩
  let C : ℝ := max C₀ 0
  have hC : ∀ k, ‖α (n k) • e (n k)‖ ≤ C := by
    intro k
    exact le_trans (hC₀ _ (Set.mem_range_self k)) (le_max_left _ _)
  have hC_nonneg : 0 ≤ C := le_max_right _ _
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.1 hα_tendsto) (C + 1)
  have hn_lt : ∀ k, n k < N := by
    intro k
    by_contra hkn
    have hlarge : C + 1 ≤ α (n k) := hN (n k) (le_of_not_gt hkn)
    have hα_nonneg : 0 ≤ α (n k) := by linarith
    have hnorm_eq : ‖α (n k) • e (n k)‖ = α (n k) := by
      rw [norm_smul, he.norm_eq_one (n k), mul_one, Real.norm_of_nonneg hα_nonneg]
    linarith [hC k, hlarge]
  let g : ℕ → {j : ℕ // j < N} := fun k ↦ ⟨n k, hn_lt k⟩
  obtain ⟨j, hjraw⟩ := Finite.exists_infinite_fiber g
  have hj : Set.Infinite {k : ℕ | g k = j} := by
    rw [Set.Infinite]
    intro hfinite
    let _ : Finite ↑(g ⁻¹' {j}) := hfinite.to_subtype
    exact Infinite.false hjraw
  refine ⟨Nat.nth (fun k ↦ g k = j), Nat.nth_strictMono hj, j.1, ?_⟩
  intro k
  have hk : g (Nat.nth (fun i ↦ g i = j) k) = j := Nat.nth_mem_of_infinite hj k
  exact congrArg Subtype.val hk

-- Proof sketch: a weakly convergent sequence in a Hilbert space is norm bounded. For a sequence in
-- `Set.range (fun n ↦ α n • e n)`, the norms are exactly the weights `α n`, so the divergence
-- `α n → +∞` forces the indices to range over a finite set. A constant subsequence argument then
-- shows the weak limit still belongs to the set.
/-- The range of a weighted orthonormal sequence with weights tending to `+∞` is weakly
sequentially closed. -/
private theorem isSeqClosed_scaled_orthonormal_range_in_weakSpace (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) (α : ℕ → ℝ) (hα_tendsto : Tendsto α atTop atTop) :
    IsSeqClosed ((toWeakSpace ℝ 𝓗) '' Set.range (fun n ↦ α n • e n)) := by
  intro u x hu hx
  classical
  have hu_exists : ∀ k, ∃ m : ℕ, u k = toWeakSpace ℝ 𝓗 (α m • e m) := by
    intro k
    rcases hu k with ⟨y, hy, hyu⟩
    rcases Set.mem_range.1 hy with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    calc
      u k = toWeakSpace ℝ 𝓗 y := hyu.symm
      _ = toWeakSpace ℝ 𝓗 (α m • e m) := by simp [hm]
  choose n hn using hu_exists
  have hseq_tendsto :
      Tendsto (fun k ↦ toWeakSpace ℝ 𝓗 (α (n k) • e (n k))) atTop (𝓝 x) := by
    exact hx.congr' (Filter.Eventually.of_forall hn)
  -- Weak convergence bounds the range, and divergence of `α` then traps the indices in a finite set.
  have hbounded : Bornology.IsBounded (Set.range fun k ↦ α (n k) • e (n k)) := by
    simpa using bounded_range_of_tendsto_weakly hseq_tendsto
  rcases exists_constant_subseq_of_bounded_scaled_orthonormal_values e he α hα_tendsto hbounded
    with ⟨φ, hφ, j, hj⟩
  have hsub_tendsto :
      Tendsto (fun k ↦ toWeakSpace ℝ 𝓗 (α (n (φ k)) • e (n (φ k)))) atTop (𝓝 x) := by
    simpa [Function.comp] using hseq_tendsto.comp hφ.tendsto_atTop
  -- Along that subsequence the weak image is constant, so Hausdorffness identifies the limit.
  have hconst_tendsto :
      Tendsto (fun _ : ℕ ↦ toWeakSpace ℝ 𝓗 (α j • e j)) atTop (𝓝 x) := by
    convert hsub_tendsto using 1
    ext k
    simp [hj k]
  have hx_eq : x = toWeakSpace ℝ 𝓗 (α j • e j) :=
    tendsto_nhds_unique hconst_tendsto tendsto_const_nhds
  exact ⟨α j • e j, Set.mem_range.2 ⟨j, rfl⟩, hx_eq.symm⟩

-- Proof sketch: describe a basic weak neighborhood of `0` using finitely many inner-product
-- inequalities. Bessel's inequality makes the resulting coefficient sequence square summable, while
-- the assumption that `∑ (α n)⁻²` diverges guarantees infinitely many indices for which
-- `α n • e n` satisfies those inequalities, so every weak neighborhood of `0` meets the set.
omit [CompleteSpace 𝓗] in
/-- Helper for Example 3.33: every weak neighborhood of `0` contains a finite tube cut out by
continuous linear functionals. -/
private lemma weakspace_zero_nhds_contains_finite_dual_tube {V : Set (WeakSpace ℝ 𝓗)}
    (hV : V ∈ 𝓝 (0 : WeakSpace ℝ 𝓗)) :
    ∃ s : Finset (StrongDual ℝ 𝓗), ∃ ε > 0,
      {x : WeakSpace ℝ 𝓗 | ∀ f ∈ s, ‖f ((toWeakSpace ℝ 𝓗).symm x)‖ < ε} ⊆ V := by
  let B : 𝓗 →ₗ[ℝ] StrongDual ℝ 𝓗 →ₗ[ℝ] ℝ := (topDualPairing ℝ 𝓗).flip
  have hbasis := LinearMap.hasBasis_weakBilin B
  rcases hbasis.mem_iff.mp hV with ⟨U, hU, hUV⟩
  rcases (SeminormFamily.basisSets_iff _).mp hU with ⟨s, ε, hε, rfl⟩
  refine ⟨s, ε, hε, ?_⟩
  intro x hx
  -- Rewrite the basic seminorm ball as simultaneous smallness for finitely many evaluations.
  have hx' : x ∈ (s.sup (LinearMap.toSeminormFamily B)).ball 0 ε := by
    rw [Seminorm.ball_finset_sup_eq_iInter _ _ _ hε]
    apply Set.mem_biInter
    intro f hf
    change x ∈
      {y : WeakSpace ℝ 𝓗 |
        (((topDualPairing ℝ 𝓗).flip.toSeminormFamily f) (y - (0 : WeakSpace ℝ 𝓗)) < ε)}
    simp only [Set.mem_setOf_eq, sub_zero]
    rw [LinearMap.toSeminormFamily_apply]
    simpa [toWeakSpace] using hx f hf
  exact hUV hx'

/-- Helper for Example 3.33: for a finite family of continuous linear functionals, the sum of their
evaluation norms on an orthonormal sequence is square-summable. -/
private lemma summable_sq_finset_dual_eval_sum (s : Finset (StrongDual ℝ 𝓗)) (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) :
    Summable (fun n ↦ (∑ f ∈ s, ‖f (e n)‖) ^ 2) := by
  have hf_sq : ∀ f : StrongDual ℝ 𝓗, Summable (fun n ↦ ‖f (e n)‖ ^ 2) := by
    intro f
    let u : 𝓗 := (InnerProductSpace.toDual ℝ 𝓗).symm f
    have hrepr : (fun n ↦ ‖f (e n)‖ ^ 2) = fun n ↦ ‖inner ℝ (e n) u‖ ^ 2 := by
      -- The Riesz representer converts each functional into inner products with a fixed vector.
      ext n
      rw [← InnerProductSpace.toDual_symm_apply]
      rw [real_inner_comm]
    rw [hrepr]
    exact he.inner_products_summable u
  have hsum : Summable (fun n ↦ ∑ f ∈ s, ‖f (e n)‖ ^ 2) := by
    classical
    -- Summability survives finite addition once each coordinate sequence is summable.
    induction s using Finset.induction_on with
    | empty =>
        simp
    | @insert a s ha ih =>
        simpa [Finset.sum_insert, ha] using (hf_sq a).add ih
  have hmajor : Summable (fun n ↦ (s.card : ℝ) * ∑ f ∈ s, ‖f (e n)‖ ^ 2) := by
    simpa [mul_comm] using hsum.mul_left (s.card : ℝ)
  -- Chebyshev's inequality controls the square of the sum by the sum of the squares.
  refine hmajor.of_nonneg_of_le (fun n ↦ sq_nonneg _) ?_
  intro n
  have hsq_sum :
      (∑ f ∈ s, ‖f (e n)‖) ^ 2 ≤ (s.card : ℝ) * ∑ f ∈ s, ‖f (e n)‖ ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq :
        (∑ f ∈ s, ‖f (e n)‖) ^ 2 ≤ (s.card : ℝ) * ∑ f ∈ s, ‖f (e n)‖ ^ 2)
  simpa using hsq_sum

/-- Helper for Example 3.33: some weighted orthonormal vector is simultaneously small on any
finite family of continuous linear functionals. -/
private lemma exists_weighted_orthonormal_vector_small_on_finite_functionals (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) (α : ℕ → ℝ) (hα_ge_one : ∀ n : ℕ, 1 ≤ α n)
    (hα_invSq_not_summable : ¬ Summable (fun n ↦ ((α n)⁻¹)^2))
    (s : Finset (StrongDual ℝ 𝓗)) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∀ f ∈ s, ‖f (α n • e n)‖ < ε := by
  let zeta : ℕ → ℝ := fun n ↦ ∑ f ∈ s, ‖f (e n)‖
  have hzeta_sq : Summable (fun n ↦ (zeta n)^2) := by
    -- This is the Bessel part of the source proof for the chosen finite family.
    simpa [zeta] using summable_sq_finset_dual_eval_sum s e he
  by_contra hnone
  have hbad : ∀ n : ℕ, ∃ f ∈ s, ε ≤ ‖f (α n • e n)‖ := by
    intro n
    by_contra hNo
    apply hnone
    refine ⟨n, ?_⟩
    intro f hf
    by_contra hge
    exact hNo ⟨f, hf, le_of_not_gt hge⟩
  have hdom : ∀ n : ℕ, ε^2 * ((α n)⁻¹)^2 ≤ (zeta n)^2 := by
    intro n
    rcases hbad n with ⟨f, hf, hfε⟩
    have hα_nonneg : 0 ≤ α n := le_trans zero_le_one (hα_ge_one n)
    have hα_pos : 0 < α n := lt_of_lt_of_le zero_lt_one (hα_ge_one n)
    have hzeta_nonneg : 0 ≤ zeta n := by
      exact Finset.sum_nonneg (fun g hg ↦ norm_nonneg _)
    have hscale : ‖f (α n • e n)‖ = α n * ‖f (e n)‖ := by
      -- Positivity of `α n` removes the absolute value from the scalar factor.
      rw [map_smul, norm_smul, Real.norm_of_nonneg hα_nonneg]
    have hterm_le : ‖f (e n)‖ ≤ zeta n := by
      let w : StrongDual ℝ 𝓗 → ℝ := fun g ↦ ‖g (e n)‖
      -- The offending coordinate is one summand of `zeta n`.
      have hw_nonneg : ∀ g ∈ s, 0 ≤ w g := fun g hg ↦ norm_nonneg _
      simpa [zeta, w] using (Finset.single_le_sum hw_nonneg hf)
    have hε_le : ε ≤ α n * zeta n := by
      calc
        ε ≤ ‖f (α n • e n)‖ := hfε
        _ = α n * ‖f (e n)‖ := hscale
        _ ≤ α n * zeta n := by gcongr
    have hdiv : ε * (α n)⁻¹ ≤ zeta n := by
      -- Divide the lower bound by the positive weight `α n`.
      rw [mul_inv_le_iff₀ hα_pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hε_le
    have hsq : (ε * (α n)⁻¹)^2 ≤ (zeta n)^2 := by
      gcongr
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
  have hsummable_inv_scaled : Summable (fun n ↦ ε^2 * ((α n)⁻¹)^2) := by
    -- Domination by the square-summable sequence `zeta n ^ 2` forces summability.
    refine hzeta_sq.of_nonneg_of_le (fun n ↦ by positivity) hdom
  have hε2_ne : ε^2 ≠ 0 := by
    positivity
  have hsummable_inv : Summable (fun n ↦ ((α n)⁻¹)^2) := by
    exact (summable_mul_left_iff hε2_ne).1 hsummable_inv_scaled
  exact hα_invSq_not_summable hsummable_inv

/-- The origin belongs to the weak closure of the range when the inverse-square weights are not
summable. -/
private theorem zero_mem_closure_scaled_orthonormal_range_in_weakSpace (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) (α : ℕ → ℝ) (hα_ge_one : ∀ n : ℕ, 1 ≤ α n)
    (hα_invSq_not_summable : ¬ Summable (fun n ↦ ((α n)⁻¹)^2)) :
    (0 : WeakSpace ℝ 𝓗) ∈ closure ((toWeakSpace ℝ 𝓗) '' Set.range (fun n ↦ α n • e n)) := by
  -- Route correction: instead of converting neighborhoods to inner-product coordinates first,
  -- extract the canonical finite family of dual functionals from the weak-topology basis.
  rw [mem_closure_iff_nhds]
  intro V hV
  rcases weakspace_zero_nhds_contains_finite_dual_tube hV with ⟨s, ε, hε, hsubset⟩
  rcases exists_weighted_orthonormal_vector_small_on_finite_functionals e he α hα_ge_one
      hα_invSq_not_summable s hε with ⟨n, hn⟩
  -- The selected weighted orthonormal vector lies in the extracted tube, hence in `V`.
  have hsmall :
      toWeakSpace ℝ 𝓗 (α n • e n) ∈
        {x : WeakSpace ℝ 𝓗 | ∀ f ∈ s, ‖f ((toWeakSpace ℝ 𝓗).symm x)‖ < ε} := by
    show ∀ f ∈ s, ‖f ((toWeakSpace ℝ 𝓗).symm (toWeakSpace ℝ 𝓗 (α n • e n)))‖ < ε
    simpa [toWeakSpace] using hn
  refine ⟨toWeakSpace ℝ 𝓗 (α n • e n), ?_⟩
  constructor
  · exact hsubset hsmall
  · exact ⟨α n • e n, Set.mem_range.2 ⟨n, rfl⟩, rfl⟩

-- Proof sketch: if `0 = α n • e n`, taking norms gives `0 = α n * ‖e n‖ = α n`, but
-- orthonormality gives `‖e n‖ = 1` and `hα_ge_one` yields `α n ≥ 1`, a contradiction.
omit [CompleteSpace 𝓗] in
/-- The origin does not belong to the range of a weighted orthonormal sequence whose weights are at
least `1`. -/
private theorem zero_not_mem_scaled_orthonormal_range (e : ℕ → 𝓗) (he : Orthonormal ℝ e)
    (α : ℕ → ℝ)
    (hα_ge_one : ∀ n : ℕ, 1 ≤ α n) :
    (0 : 𝓗) ∉ Set.range (fun n ↦ α n • e n) := by
  rintro hx
  rcases Set.mem_range.1 hx with ⟨n, hn⟩
  have hα_nonneg : 0 ≤ α n := le_trans zero_le_one (hα_ge_one n)
  -- Taking norms turns the equation `0 = α n • e n` into the contradiction `0 = α n ≥ 1`.
  have hnorm_eq : ‖α n • e n‖ = α n := by
    rw [norm_smul, he.norm_eq_one n, mul_one, Real.norm_of_nonneg hα_nonneg]
  have hα_zero : α n = 0 := by
    calc
      α n = ‖α n • e n‖ := hnorm_eq.symm
      _ = ‖(0 : 𝓗)‖ := by simp [hn]
      _ = 0 := norm_zero
  have hcontr : (1 : ℝ) ≤ 0 := by
    simpa [hα_zero] using hα_ge_one n
  linarith

-- Proof sketch: combine the weak sequential closedness statement with the fact that `0` lies in
-- the weak closure but not in the set itself; a weakly closed set would contain all points of its
-- weak closure.
/-- Example 3.33: for `C = {α n • e n | n : ℕ}` coming from an orthonormal sequence and a
monotone weight sequence in `[1, +∞)` tending to `+∞` with non-summable inverse squares, `C` is
norm closed and weakly sequentially closed, is not weakly closed, and satisfies
`0 ∈ closure ((toWeakSpace ℝ 𝓗) '' C)` and `0 ∉ C`. -/
theorem scaled_orthonormal_range_weaklySeqClosed_and_not_weaklyClosed (e : ℕ → 𝓗)
    (he : Orthonormal ℝ e) (α : ℕ → ℝ) (hα_ge_one : ∀ n : ℕ, 1 ≤ α n)
    (_hα_monotone : Monotone α) (hα_tendsto : Tendsto α atTop atTop)
    (hα_invSq_not_summable : ¬ Summable (fun n ↦ ((α n)⁻¹)^2)) :
    IsClosed (Set.range (fun n ↦ α n • e n)) ∧
      IsSeqClosed ((toWeakSpace ℝ 𝓗) '' Set.range (fun n ↦ α n • e n)) ∧
      ¬ IsClosed ((toWeakSpace ℝ 𝓗) '' Set.range (fun n ↦ α n • e n)) ∧
      (0 : WeakSpace ℝ 𝓗) ∈ closure ((toWeakSpace ℝ 𝓗) '' Set.range (fun n ↦ α n • e n)) ∧
      (0 : 𝓗) ∉ Set.range (fun n ↦ α n • e n) := by
  have hseqClosed :
      IsSeqClosed ((toWeakSpace ℝ 𝓗) '' Set.range (fun n ↦ α n • e n)) :=
    isSeqClosed_scaled_orthonormal_range_in_weakSpace e he α hα_tendsto
  have hzero_mem_closure :
      (0 : WeakSpace ℝ 𝓗) ∈ closure ((toWeakSpace ℝ 𝓗) '' Set.range (fun n ↦ α n • e n)) :=
    zero_mem_closure_scaled_orthonormal_range_in_weakSpace e he α hα_ge_one
      hα_invSq_not_summable
  have hzero_not_mem : (0 : 𝓗) ∉ Set.range (fun n ↦ α n • e n) :=
    zero_not_mem_scaled_orthonormal_range e he α hα_ge_one
  refine ⟨isClosed_scaled_orthonormal_range e he α hα_ge_one, hseqClosed, ?_, hzero_mem_closure,
    hzero_not_mem⟩
  intro hclosed
  have hzero_mem :
      (0 : WeakSpace ℝ 𝓗) ∈ ((toWeakSpace ℝ 𝓗) '' Set.range (fun n ↦ α n • e n)) := by
    rw [← hclosed.closure_eq]
    exact hzero_mem_closure
  rcases hzero_mem with ⟨y, hy, hy0⟩
  have hy_zero : y = 0 := (toWeakSpace ℝ 𝓗).injective (by simpa using hy0)
  exact hzero_not_mem (hy_zero ▸ hy)

/-! Source item: AttouchPeypouquetRedont2014 items/ext_def_3 -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Sequential continuity for the canonical weak topology. -/
def IsWeakToWeakSequentiallyContinuous (T : H → H) : Prop :=
  ∀ x : ℕ → H, ∀ x₀ : H,
    Filter.Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) Filter.atTop
        (nhds (toWeakSpace ℝ H x₀)) →
    Filter.Tendsto (fun n ↦ toWeakSpace ℝ H (T (x n))) Filter.atTop
        (nhds (toWeakSpace ℝ H (T x₀)))

/-! Source item: Attouch_Asymptotic_behavior_of_Newton_like_inertial_dynamics_involving_the_sum_of_potential_and_nonpotential_terms_2021 items/ext_def_4 -/

/-- A weak sequential cluster point of a continuous-time trajectory `x : ℝ → H`:
some time sequence `t : ℕ → ℝ` tending to infinity pulls back `x` to a sequence
converging weakly to `p`. -/
def IsWeakSequentialClusterPoint (x : ℝ → H) (p : H) : Prop :=
  ∃ t : ℕ → ℝ, Filter.Tendsto t Filter.atTop Filter.atTop ∧
    Filter.Tendsto (fun n => toWeakSpace ℝ H (x (t n))) Filter.atTop
      (nhds (toWeakSpace ℝ H p))


/-! ### Continuous-time Opial lemma

Continuous-time companion of `opial_lemma` for trajectories `x : ℝ → H`.

Promoted from `Attouch_Bot_Csetnek_Closed_loop_damping_2023` (ext_thm_7).
-/

open Filter


private theorem opial_for_time_sequence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S : Set H) (hS : S.Nonempty) (x : ℝ → H)
    (hdist : ∀ z ∈ S, ∃ l : ℝ, Tendsto (fun t ↦ ‖x t - z‖) atTop (nhds l))
    (hcluster : ∀ z, (∃ u : ℕ → ℝ, Tendsto u atTop atTop ∧
      ∀ v : H, Tendsto (fun n ↦ inner ℝ (x (u n)) v) atTop (nhds (inner ℝ z v))) → z ∈ S)
    (τ : ℕ → ℝ) (hτ : Tendsto τ atTop atTop) :
    ∃ z ∈ S, Tendsto (fun n ↦ toWeakSpace ℝ H (x (τ n))) atTop
      (nhds (toWeakSpace ℝ H z)) := by
  refine opial_lemma hS (fun n ↦ x (τ n)) ?_ ?_
  · intro z hz
    rcases hdist z hz with ⟨l, hl⟩
    exact ⟨l, by simpa [Function.comp_def] using hl.comp hτ⟩
  · intro z hz
    rcases hz.exists_subseq_tendsto with ⟨φ, hφ, hφweak⟩
    let ψ : ℕ → ℝ := τ ∘ φ
    have hψ : Tendsto ψ atTop atTop := by
      simpa [ψ, Function.comp_def] using hτ.comp hφ.tendsto_atTop
    have hψweak : ∀ v : H, Tendsto (fun n ↦ inner ℝ (x (ψ n)) v) atTop
        (nhds (inner ℝ z v)) := by
      simpa [ψ, Function.comp_def] using
        (weakConvergence_iff_forall_tendsto_inner_right (fun n ↦ x (τ (φ n))) z).1 hφweak
    exact hcluster z ⟨ψ, hψ, hψweak⟩

private theorem real_tendsto_atTop_of_all_divergent_sequences {f : ℝ → ℝ} {a : ℝ}
    (h : ∀ t : ℕ → ℝ, Tendsto t atTop atTop → Tendsto (f ∘ t) atTop (nhds a)) :
    Tendsto f atTop (nhds a) := by
  by_contra hf
  rw [Metric.tendsto_atTop] at hf
  push Not at hf
  rcases hf with ⟨ε, hε, hbad⟩
  choose s hs_ge hs_bad using hbad
  let t : ℕ → ℝ := fun n ↦ s n
  have ht : Tendsto t atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro R
    obtain ⟨N, hN⟩ := exists_nat_ge R
    refine ⟨N, fun n hn ↦ le_trans (le_trans hN (Nat.cast_le.2 hn)) (hs_ge n)⟩
  have hconv := h t ht
  rw [Metric.tendsto_atTop] at hconv
  rcases hconv ε hε with ⟨N, hN⟩
  exact (not_lt_of_ge (hs_bad N)) (by simpa [Function.comp, t] using hN N le_rfl)

private theorem interleave_tendsto_atTop (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) :
    Tendsto (fun n : ℕ ↦ if Even n then ((n / 2 : ℕ) : ℝ) else t (n / 2)) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro R
  obtain ⟨N, hN⟩ := exists_nat_ge R
  rcases (eventually_atTop.1 (ht.eventually (eventually_ge_atTop R))) with ⟨M, hM⟩
  refine ⟨2 * max N M, ?_⟩
  intro k hk
  have hdiv : max N M ≤ k / 2 := by omega
  by_cases he : Even k
  · simp [he]
    exact le_trans hN (Nat.cast_le.2 (le_trans (le_max_left _ _) hdiv))
  · simp [he]
    exact hM _ (le_trans (le_max_right _ _) hdiv)

/-- Continuous-time Opial lemma for a bounded Hilbert trajectory.  Named
`opial_lemma_continuous` rather than `continuous_opial_lemma` because the
root-level name `continuous_opial_lemma` is taken by a paper-local declaration
(`Attouch_RATE_..._2017/items/ext_lem_2`). -/
theorem opial_lemma_continuous {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (x : ℝ → H) (S : Set H) (hS : S.Nonempty) (_hbounded : Bornology.IsBounded (Set.range x))
    (hdist : ∀ z ∈ S, ∃ l, Filter.Tendsto (fun t ↦ ‖x t - z‖) Filter.atTop (nhds l))
    (hcluster : ∀ z, (∃ tₙ : ℕ → ℝ, Filter.Tendsto tₙ Filter.atTop Filter.atTop ∧
      ∀ y : H, Filter.Tendsto (fun n ↦ inner ℝ (x (tₙ n)) y)
        Filter.atTop (nhds (inner ℝ z y))) → z ∈ S) :
    ∃ z ∈ S, ∀ y, Filter.Tendsto (fun t ↦ inner ℝ (x t) y) Filter.atTop (nhds (inner ℝ z y)) := by
  have hnat_time : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  obtain ⟨z, hzS, hz_nat⟩ :=
    opial_for_time_sequence S hS x hdist hcluster (fun n : ℕ ↦ (n : ℝ)) hnat_time
  have h_all_sequences : ∀ t : ℕ → ℝ, Tendsto t atTop atTop →
      Tendsto (fun n ↦ toWeakSpace ℝ H (x (t n))) atTop (nhds (toWeakSpace ℝ H z)) := by
    intro t ht
    let q : ℕ → ℝ := fun n ↦ if Even n then ((n / 2 : ℕ) : ℝ) else t (n / 2)
    have hq : Tendsto q atTop atTop := by
      simpa [q] using interleave_tendsto_atTop t ht
    obtain ⟨w, hwS, hqweak⟩ := opial_for_time_sequence S hS x hdist hcluster q hq
    have hEven : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro N
      exact ⟨N, fun n hn ↦ by omega⟩
    have hOdd : Tendsto (fun n : ℕ ↦ 2 * n + 1) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro N
      exact ⟨N, fun n hn ↦ by omega⟩
    have hq_even : ∀ n : ℕ, q (2 * n) = (n : ℝ) := by
      intro n
      simp only [q, if_pos (even_two_mul n)]
      norm_cast
      omega
    have hq_odd : ∀ n : ℕ, q (2 * n + 1) = t n := by
      intro n
      simp only [q, if_neg (Nat.not_even_two_mul_add_one n)]
      congr 1
      omega
    have hnat_w : Tendsto (fun n : ℕ ↦ toWeakSpace ℝ H (x (n : ℝ))) atTop
        (nhds (toWeakSpace ℝ H w)) := by
      convert hqweak.comp hEven using 1
      ext n
      simp [Function.comp, hq_even]
    have hzw : z = w :=
      (toWeakSpace ℝ H).injective (tendsto_nhds_unique hz_nat hnat_w)
    have ht_w : Tendsto (fun n ↦ toWeakSpace ℝ H (x (t n))) atTop
        (nhds (toWeakSpace ℝ H w)) := by
      convert hqweak.comp hOdd using 1
      ext n
      simp [Function.comp, hq_odd]
    simpa [hzw] using ht_w
  refine ⟨z, hzS, ?_⟩
  intro y
  apply real_tendsto_atTop_of_all_divergent_sequences
  intro t ht
  exact (weakConvergence_iff_forall_tendsto_inner_right (fun n ↦ x (t n)) z).1
    (h_all_sequences t ht) y


/-! ### Continuous-time Opial lemma, weak form

Continuous-time Opial lemma for a Hilbert trajectory **without** a boundedness
hypothesis, stated in the weak topology: weak sequential cluster points (given
by continuous linear functionals) of the trajectory lie in `S`, and the
trajectory converges weakly to a point of `S`.  Strictly more general than
`opial_lemma_continuous` (whose `_hbounded` hypothesis is unused in its proof
and whose cluster/conclusion forms use the inner product).

Promoted from
`Attouch_Asymptotic_stabilization_of_inertial_gradient_dynamics_with_time_dependent_viscosity_2017`
(ext_lem_1).
-/

/-- Weak tendsto (in the weak topology) of a sequence implies that every
  continuous linear functional applied to the sequence tends to its value at
  the limit. -/
theorem tendsto_apply_of_tendsto_toWeakSpace
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {x : ℕ → H} {z : H}
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (nhds (toWeakSpace ℝ H z)))
    (f : H →L[ℝ] ℝ) : Tendsto (fun n ↦ f (x n)) atTop (nhds (f z)) := by
  let y : H := (InnerProductSpace.toDual ℝ H).symm f
  have hy : ∀ v : H, f v = inner ℝ y v := by
    intro v
    symm
    exact InnerProductSpace.toDual_symm_apply
  simpa only [hy, real_inner_comm] using
    (weakConvergence_iff_forall_tendsto_inner_right x z).1 hweak y

/-- Time-sequence Opial lemma in weak (functional) form: if every cluster point
  of every subsequence along a diverging time sequence (in the weak topology,
  given by continuous linear functionals) lies in `S`, then the time subsequence
  converges weakly to a point of `S`.  Weak form of the private
  `opial_for_time_sequence` (inner-product form). -/
theorem opial_for_time_sequence_weak
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (S : Set H) (hS : S.Nonempty) (x : ℝ → H)
    (hdist : ∀ z ∈ S, ∃ l : ℝ, Tendsto (fun t ↦ ‖x t - z‖) atTop (nhds l))
    (hcluster : ∀ z, (∃ u : ℕ → ℝ, Tendsto u atTop atTop ∧
      ∀ f : H →L[ℝ] ℝ, Tendsto (fun n ↦ f (x (u n))) atTop (nhds (f z))) → z ∈ S)
    (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) :
    ∃ z ∈ S, Tendsto (fun n ↦ toWeakSpace ℝ H (x (t n))) atTop
      (nhds (toWeakSpace ℝ H z)) := by
  refine opial_lemma hS (fun n ↦ x (t n)) ?_ ?_
  · intro z hz
    rcases hdist z hz with ⟨l, hl⟩
    exact ⟨l, by simpa [Function.comp_def] using hl.comp ht⟩
  · intro z hz
    rcases hz.exists_subseq_tendsto with ⟨φ, hφ, hφweak⟩
    apply hcluster z
    refine ⟨t ∘ φ, ?_, ?_⟩
    · simpa [Function.comp_def] using ht.comp hφ.tendsto_atTop
    · intro f
      exact tendsto_apply_of_tendsto_toWeakSpace hφweak f

/-- Continuous-time Opial lemma in weak (functional) form, without a boundedness
  hypothesis.  Weak form of `opial_lemma_continuous`; the trajectory converges
  weakly (all continuous linear functionals tend) to a point of `S`. -/
theorem opial_lemma_continuous_weak {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (x : ℝ → H) (S : Set H) (hS : S.Nonempty)
    (hdist : ∀ z ∈ S, ∃ l : ℝ, Tendsto (fun t => ‖x t - z‖) atTop (nhds l))
    (hcluster : ∀ z, (∃ u : ℕ → ℝ, Tendsto u atTop atTop ∧
      ∀ f : H →L[ℝ] ℝ, Tendsto (fun n => f (x (u n))) atTop (nhds (f z))) → z ∈ S) :
    ∃ z ∈ S, ∀ f : H →L[ℝ] ℝ, Tendsto (fun t => f (x t)) atTop (nhds (f z)) := by
  have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := by
    simpa using (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)
  obtain ⟨z, hzS, hz_nat⟩ :=
    opial_for_time_sequence_weak S hS x hdist hcluster (fun n : ℕ ↦ (n : ℝ)) hnat
  have h_all_sequences : ∀ t : ℕ → ℝ, Tendsto t atTop atTop →
      Tendsto (fun n ↦ toWeakSpace ℝ H (x (t n))) atTop (nhds (toWeakSpace ℝ H z)) := by
    intro t ht
    let q : ℕ → ℝ := fun n ↦ if Even n then ((n / 2 : ℕ) : ℝ) else t (n / 2)
    have hq : Tendsto q atTop atTop := by
      simpa [q] using interleave_tendsto_atTop t ht
    obtain ⟨w, hwS, hqweak⟩ := opial_for_time_sequence_weak S hS x hdist hcluster q hq
    have hEven : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro N
      exact ⟨N, fun n hn ↦ by omega⟩
    have hOdd : Tendsto (fun n : ℕ ↦ 2 * n + 1) atTop atTop := by
      rw [Filter.tendsto_atTop_atTop]
      intro N
      exact ⟨N, fun n hn ↦ by omega⟩
    have hq_even : ∀ n : ℕ, q (2 * n) = (n : ℝ) := by
      intro n
      simp only [q, if_pos (even_two_mul n)]
      norm_cast
      omega
    have hq_odd : ∀ n : ℕ, q (2 * n + 1) = t n := by
      intro n
      simp only [q, if_neg (Nat.not_even_two_mul_add_one n)]
      congr 1
      omega
    have hnat_w : Tendsto (fun n : ℕ ↦ toWeakSpace ℝ H (x (n : ℝ))) atTop
        (nhds (toWeakSpace ℝ H w)) := by
      convert hqweak.comp hEven using 1
      ext n
      simp [Function.comp, hq_even]
    have hzw : z = w :=
      (toWeakSpace ℝ H).injective (tendsto_nhds_unique hz_nat hnat_w)
    have ht_w : Tendsto (fun n ↦ toWeakSpace ℝ H (x (t n))) atTop
        (nhds (toWeakSpace ℝ H w)) := by
      convert hqweak.comp hOdd using 1
      ext n
      simp [Function.comp, hq_odd]
    simpa [hzw] using ht_w
  refine ⟨z, hzS, ?_⟩
  intro f
  apply real_tendsto_atTop_of_all_divergent_sequences
  intro t ht
  exact tendsto_apply_of_tendsto_toWeakSpace (h_all_sequences t ht) f


/-! ### Mosco convergence

Mosco convergence of a sequence of functions: weak lower bound plus strong
recovery sequences.  Standard epigraphical-convergence notion in variational
analysis.

Promoted from `Attouch_Bot_Csetnek_Closed_loop_damping_2023` (ext_def_4).
-/

/-- Mosco convergence: weak lower bound plus strong recovery sequences. -/
def MoscoConverges {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ψ : ℕ → H → ℝ) (Φ : H → ℝ) : Prop :=
  (∀ n, ConvexOn ℝ Set.univ (Ψ n) ∧ LowerSemicontinuous (Ψ n) ∧ ∃ x, Ψ n x = Ψ n x) ∧
  ConvexOn ℝ Set.univ Φ ∧ LowerSemicontinuous Φ ∧ (∃ x, Φ x = Φ x) ∧
  (∀ (xₙ : ℕ → H) x, (∀ y, Filter.Tendsto (fun n ↦ inner ℝ (xₙ n) y) Filter.atTop
      (nhds (inner ℝ x y))) →
    Φ x ≤ Filter.liminf (fun n ↦ Ψ n (xₙ n)) Filter.atTop) ∧
  ∀ x, ∃ xₙ : ℕ → H, Filter.Tendsto xₙ Filter.atTop (nhds x) ∧
    Filter.Tendsto (fun n ↦ Ψ n (xₙ n)) Filter.atTop (nhds (Φ x))
