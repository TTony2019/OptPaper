import Mathlib
import Mathlib.Data.List.TFAE
import Foundation.Projection.BestApproximation

/-!
# Operator Linear

Linear and continuous linear operator theory, adjoints, positivity/monotonicity, weak dual tests, and Moore-Penrose inverse axioms.
-/

open _root_.ContinuousLinearMap _root_.IsSelfAdjoint _root_.LinearMap
open scoped InnerProductSpace
open InnerProductSpace
open scoped InnerProduct InnerProductSpace
open ContinuousLinearMap

/-! Source item: Chap02/Fact_2_20 -/
universe u v

namespace LinearMap

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private lemma continuousAt_zero_of_exists_continuousAt
    (T : X →ₗ[ℝ] Y) (hT : ∃ x₀ : X, ContinuousAt T x₀) : ContinuousAt T 0 := by
  rcases hT with ⟨x₀, hx₀⟩
  have hshift : ContinuousAt (fun z : X ↦ T (x₀ + z) - T x₀) 0 := by
    have hTx₀ : ContinuousAt T (x₀ + 0) := by
      simpa using hx₀
    exact (hTx₀.comp <| continuousAt_const.add continuousAt_id).sub continuousAt_const
  simpa [LinearMap.map_add] using hshift

/-- A real linear map is continuous if and only if it is globally Lipschitz. -/
theorem continuous_iff_exists_lipschitzWith (T : X →ₗ[ℝ] Y) :
    Continuous T ↔ ∃ K : NNReal, LipschitzWith K T := by
  constructor
  · intro hT
    let T' : X →L[ℝ] Y := ⟨T, hT⟩
    refine ⟨‖T'‖₊, ?_⟩
    simpa [T'] using T'.lipschitz
  · rintro ⟨K, hK⟩
    exact hK.continuous

end LinearMap

/-- Fact 2.20 in the textbook phrasing: a real linear map is continuous at some point if and only
if it is globally Lipschitz. -/
theorem linearMap_continuousAt_some_iff_exists_lipschitz_constant
    {X : Type u} {Y : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →ₗ[ℝ] Y) :
    (∃ x₀ : X, ContinuousAt T x₀) ↔ ∃ K : NNReal, LipschitzWith K T := by
  constructor
  · intro hT
    exact (LinearMap.continuous_iff_exists_lipschitzWith T).mp <|
      continuous_of_continuousAt_zero T <|
        LinearMap.continuousAt_zero_of_exists_continuousAt T hT
  · intro hT
    exact ⟨0, (LinearMap.continuous_iff_exists_lipschitzWith T).mpr hT |>.continuousAt⟩

/-- Fact 2.20 in the textbook norm-inequality form. -/
theorem linearMap_continuousAt_some_iff_exists_nonneg_real_lipschitz_constant
    {X : Type u} {Y : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →ₗ[ℝ] Y) :
    (∃ x₀ : X, ContinuousAt T x₀) ↔
      ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : X, ‖T x - T y‖ ≤ L * ‖x - y‖ := by
  rw [linearMap_continuousAt_some_iff_exists_lipschitz_constant]
  constructor
  · rintro ⟨K, hK⟩
    refine ⟨K, K.2, ?_⟩
    intro x y
    simpa [dist_eq_norm] using hK.dist_le_mul x y
  · rintro ⟨L, hL, hT⟩
    refine ⟨Real.toNNReal L, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    simpa [dist_eq_norm, Real.toNNReal_of_nonneg hL] using hT x y

/-! Source item: Chap02/Fact_2_21 -/
universe w

namespace LinearMap

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

private lemma continuous_uncurry_of_norm_bound₂ (T : X →ₗ[ℝ] Y →ₗ[ℝ] Z) {β : ℝ}
    (hβ : ∀ x y, ‖T x y‖ ≤ β * ‖x‖ * ‖y‖) :
    Continuous (Function.uncurry fun x y ↦ T x y) := by
  -- Package the bilinear map as a continuous bilinear map with the same pointwise values.
  simpa [LinearMap.mkContinuous₂_apply] using
    (T.mkContinuous₂ β hβ).continuous₂

private lemma norm_bound₂_of_small_ball_control (T : X →ₗ[ℝ] Y →ₗ[ℝ] Z) {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ x y, ‖x‖ ≤ r → ‖y‖ ≤ r → ‖T x y‖ ≤ 1) :
    ∃ β : ℝ, 0 ≤ β ∧ ∀ x y, ‖T x y‖ ≤ β * ‖x‖ * ‖y‖ := by
  have hβ0 : 0 ≤ r⁻¹ * r⁻¹ := by positivity
  refine ⟨r⁻¹ * r⁻¹, hβ0, ?_⟩
  intro x y
  by_cases hx : x = 0
  · -- If the first variable vanishes, bilinearity forces the value to vanish.
    simp [hx]
  by_cases hy : y = 0
  · -- If the second variable vanishes, bilinearity again forces the value to vanish.
    simp [hy]
  have hxnorm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hynorm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  let x' : X := (r / ‖x‖) • x
  let y' : Y := (r / ‖y‖) • y
  have hx'_norm : ‖x'‖ = r := by
    -- The normalization sends `x` to the sphere of radius `r`.
    calc
      ‖x'‖ = ‖(r / ‖x‖ : ℝ)‖ * ‖x‖ := by simp [x', norm_smul]
      _ = (r / ‖x‖) * ‖x‖ := by
        rw [Real.norm_of_nonneg (div_nonneg hr.le (norm_nonneg x))]
      _ = r := by
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hxnorm_pos.ne', mul_one]
  have hy'_norm : ‖y'‖ = r := by
    -- The same normalization argument works for `y`.
    calc
      ‖y'‖ = ‖(r / ‖y‖ : ℝ)‖ * ‖y‖ := by simp [y', norm_smul]
      _ = (r / ‖y‖) * ‖y‖ := by
        rw [Real.norm_of_nonneg (div_nonneg hr.le (norm_nonneg y))]
      _ = r := by
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hynorm_pos.ne', mul_one]
  have hx'_le : ‖x'‖ ≤ r := by simp [hx'_norm]
  have hy'_le : ‖y'‖ ≤ r := by simp [hy'_norm]
  have hxy'_bound : ‖T x' y'‖ ≤ 1 := hsmall x' y' hx'_le hy'_le
  have hx_scale : (‖x‖ / r) • x' = x := by
    -- Rescaling back recovers the original vector.
    calc
      (‖x‖ / r) • x' = ((‖x‖ / r) * (r / ‖x‖)) • x := by simp [x', smul_smul]
      _ = (1 : ℝ) • x := by
        congr 1
        field_simp [hxnorm_pos.ne', hr.ne']
      _ = x := one_smul ℝ x
  have hy_scale : (‖y‖ / r) • y' = y := by
    -- Rescaling back recovers the second vector as well.
    calc
      (‖y‖ / r) • y' = ((‖y‖ / r) * (r / ‖y‖)) • y := by simp [y', smul_smul]
      _ = (1 : ℝ) • y := by
        congr 1
        field_simp [hynorm_pos.ne', hr.ne']
      _ = y := one_smul ℝ y
  have hsmul₂ :
      ∀ (a b : ℝ) (u : X) (v : Y), T (a • u) (b • v) = (a * b) • T u v := by
    intro a b u v
    -- Bilinearity converts separate scalar rescalings into a single product scalar.
    rw [map_smul, map_smul]
    simp [smul_smul, mul_comm]
  have hxy_expand :
      T x y = ((‖x‖ / r) * (‖y‖ / r)) • T x' y' := by
    -- Bilinearity turns the rescaling into a scalar factor on the value.
    calc
      T x y = T ((‖x‖ / r) • x') ((‖y‖ / r) • y') := by rw [hx_scale, hy_scale]
      _ = ((‖x‖ / r) * (‖y‖ / r)) • T x' y' := by
        simpa using hsmul₂ (‖x‖ / r) (‖y‖ / r) x' y'
  have hcoeff_nonneg : 0 ≤ (‖x‖ / r) * (‖y‖ / r) := by
    exact mul_nonneg (div_nonneg (norm_nonneg x) hr.le) (div_nonneg (norm_nonneg y) hr.le)
  calc
    ‖T x y‖ = ‖((‖x‖ / r) * (‖y‖ / r)) • T x' y'‖ := by rw [hxy_expand]
    _ = ((‖x‖ / r) * (‖y‖ / r)) * ‖T x' y'‖ := by
      rw [norm_smul, Real.norm_of_nonneg hcoeff_nonneg]
    _ ≤ ((‖x‖ / r) * (‖y‖ / r)) * 1 := by
      gcongr
    _ = (r⁻¹ * r⁻¹) * ‖x‖ * ‖y‖ := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring

private lemma norm_bound₂_of_continuousAt_zero_uncurry (T : X →ₗ[ℝ] Y →ₗ[ℝ] Z)
    (hT : ContinuousAt (Function.uncurry fun x y ↦ T x y) (0, 0)) :
    ∃ β : ℝ, 0 ≤ β ∧ ∀ x y, ‖T x y‖ ≤ β * ‖x‖ * ‖y‖ := by
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuousAt_iff.mp hT) 1 zero_lt_one
  have hr : 0 < δ / 2 := by positivity
  refine norm_bound₂_of_small_ball_control T hr ?_
  intro x y hx hy
  have hpair_lt : dist (x, y) (0, 0) < δ := by
    -- Bounds on each coordinate control the product norm.
    rw [Prod.dist_eq]
    have hmax : max ‖x‖ ‖y‖ ≤ δ / 2 := max_le hx hy
    simpa [dist_eq_norm] using lt_of_le_of_lt hmax (by linarith)
  have hvalue_lt : dist (T x y) (T 0 0) < 1 := hδ hpair_lt
  -- Since a bilinear map sends `(0,0)` to `0`, the image lies in the unit ball.
  simpa [dist_eq_norm] using le_of_lt hvalue_lt

/-- Fact 2.21 in bundled form: a bilinear map is continuous exactly when it comes from a
`ContinuousLinearMap` with the same pointwise values. -/
theorem continuous_uncurry_iff_exists_continuousLinearMap (T : X →ₗ[ℝ] Y →ₗ[ℝ] Z) :
    Continuous (Function.uncurry fun x y ↦ T x y) ↔
      ∃ S : X →L[ℝ] Y →L[ℝ] Z, ∀ x y, S x y = T x y := by
  constructor
  · intro hT
    obtain ⟨β, -, hβ⟩ := norm_bound₂_of_continuousAt_zero_uncurry T hT.continuousAt
    exact ⟨T.mkContinuous₂ β hβ, fun x y ↦ rfl⟩
  · rintro ⟨S, hS⟩
    simpa [Function.uncurry, hS] using S.continuous₂

/-- Fact 2.21: for a bilinear map already packaged as `T : X →ₗ[ℝ] Y →ₗ[ℝ] Z`, continuity of the
uncurried map is equivalent to the unbundled library predicate `IsBoundedBilinearMap`. This is a
thin bridge from the bundled `ContinuousLinearMap` criterion. -/
theorem isBoundedBilinearMap_uncurry_iff_continuous (T : X →ₗ[ℝ] Y →ₗ[ℝ] Z) :
    IsBoundedBilinearMap ℝ (Function.uncurry fun x y ↦ T x y) ↔
      Continuous (Function.uncurry fun x y ↦ T x y) := by
  constructor
  · intro hT
    exact hT.continuous
  · intro hT
    rcases (continuous_uncurry_iff_exists_continuousLinearMap T).mp hT with ⟨S, hS⟩
    simpa [Function.uncurry, hS] using S.isBoundedBilinearMap

/-- The textbook norm estimate in Fact 2.21, presented in the library-facing `Function.uncurry`
form and with the canonical existential `∃ β` rather than a separate nonnegativity conjunct. -/
theorem continuous_uncurry_iff_exists_bound₂ (T : X →ₗ[ℝ] Y →ₗ[ℝ] Z) :
    Continuous (Function.uncurry fun x y ↦ T x y) ↔
      ∃ β : ℝ, ∀ x y, ‖T x y‖ ≤ β * ‖x‖ * ‖y‖ := by
  constructor
  · intro hT
    obtain ⟨β, -, hβ⟩ := norm_bound₂_of_continuousAt_zero_uncurry T hT.continuousAt
    exact ⟨β, hβ⟩
  · rintro ⟨β, hβ⟩
    exact continuous_uncurry_of_norm_bound₂ T hβ

-- Proof sketch: use the same unit-ball argument as in the global continuity criterion, noting
-- that bilinearity reduces continuity everywhere to continuity at the origin.
/-- Continuity of a bilinear map at the origin is equivalent to the existence of a global bilinear
norm bound. -/
theorem continuousAt_zero_uncurry_iff_exists_bound₂ (T : X →ₗ[ℝ] Y →ₗ[ℝ] Z) :
    ContinuousAt (Function.uncurry fun x y ↦ T x y) (0, 0) ↔
      ∃ β : ℝ, ∀ x y, ‖T x y‖ ≤ β * ‖x‖ * ‖y‖ := by
  constructor
  · intro hT
    -- The converse engine is the local estimate obtained from continuity at the origin.
    obtain ⟨β, -, hβ⟩ := norm_bound₂_of_continuousAt_zero_uncurry T hT
    exact ⟨β, hβ⟩
  · rintro ⟨β, hβ⟩
    -- The forward bound already gives global continuity, hence continuity at `(0,0)`.
    exact (continuous_uncurry_of_norm_bound₂ T hβ).continuousAt

end LinearMap

/-! Source item: Chap02/Definition_2_23 -/


namespace LinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Definition 2.23 (1): a linear operator on a real Hilbert space is monotone when
`⟪T x, x⟫_ℝ` is nonnegative for every vector `x`. -/
def IsMonotone (T : H →ₗ[ℝ] H) : Prop :=
  ∀ x, 0 ≤ ⟪T x, x⟫_ℝ

/-- For real Hilbert spaces, positivity is exactly symmetry together with the monotonicity
inequality from Definition 2.23 (1). -/
theorem isPositive_iff_isSymmetric_and_isMonotone (T : H →ₗ[ℝ] H) :
    T.IsPositive ↔ T.IsSymmetric ∧ IsMonotone T := by
  simpa [IsMonotone] using (LinearMap.isPositive_iff T)

/-- A positive linear operator is monotone after forgetting the symmetry part of positivity. -/
theorem IsPositive.isMonotone {T : H →ₗ[ℝ] H} (hT : T.IsPositive) :
    IsMonotone T := by
  simpa [IsMonotone] using hT.inner_nonneg_left

/-- Definition 2.23 (2): a linear operator on a real Hilbert space is strictly monotone when
`⟪T x, x⟫_ℝ` is strictly positive for every nonzero vector `x`. -/
def IsStrictlyMonotone (T : H →ₗ[ℝ] H) : Prop :=
  ∀ x, x ≠ 0 → 0 < ⟪T x, x⟫_ℝ

/-- A strictly monotone linear operator is monotone. -/
theorem IsStrictlyMonotone.isMonotone {T : H →ₗ[ℝ] H} (hT : IsStrictlyMonotone T) :
    IsMonotone T := by
  change ∀ x, 0 ≤ ⟪T x, x⟫_ℝ
  intro x
  by_cases hx : x = 0
  · subst x
    simp
  · exact le_of_lt (hT x hx)

/-- Definition 2.23 (3): for a positive real scalar `α`, a linear operator on a real Hilbert
space is `α`-strongly monotone when `⟪T x, x⟫_ℝ` dominates `α * ‖x‖ ^ 2` for every vector `x`. -/
def IsStronglyMonotone (T : H →ₗ[ℝ] H) (α : ℝ) : Prop :=
  0 < α ∧ ∀ x, α * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ

/-- The parameter of a strongly monotone operator is positive. -/
theorem IsStronglyMonotone.pos {T : H →ₗ[ℝ] H} {α : ℝ} (hT : IsStronglyMonotone T α) :
    0 < α :=
  hT.1

/-- A strongly monotone operator satisfies the textbook lower bound at every vector. -/
theorem IsStronglyMonotone.ineq {T : H →ₗ[ℝ] H} {α : ℝ} (hT : IsStronglyMonotone T α)
    (x : H) :
    α * ‖x‖ ^ 2 ≤ ⟪T x, x⟫_ℝ :=
  hT.2 x

/-- An `α`-strongly monotone linear operator is strictly monotone. -/
theorem IsStronglyMonotone.isStrictlyMonotone {T : H →ₗ[ℝ] H} {α : ℝ}
    (hT : IsStronglyMonotone T α) :
    IsStrictlyMonotone T := by
  change ∀ x, x ≠ 0 → 0 < ⟪T x, x⟫_ℝ
  intro x hx
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsq : 0 < ‖x‖ ^ 2 := pow_pos hnorm 2
  have hlower : 0 < α * ‖x‖ ^ 2 := mul_pos hT.pos hsq
  exact lt_of_lt_of_le hlower (hT.ineq x)

/-- An `α`-strongly monotone linear operator is monotone. -/
theorem IsStronglyMonotone.isMonotone {T : H →ₗ[ℝ] H} {α : ℝ}
    (hT : IsStronglyMonotone T α) :
    IsMonotone T :=
  hT.isStrictlyMonotone.isMonotone

end LinearMap

/-! Source item: Chap02/Fact_2_24 -/


variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Fact 2.24: every continuous linear functional on a real Hilbert space is represented by a
unique vector through the inner product, and the representing vector has the same norm as the
functional. -/
-- Proof sketch: the representing vector is `(toDual ℝ H).symm f`; rewrite the Riesz equation
-- pointwise via the inner product, and use injectivity of `toDual` for uniqueness.
theorem riesz_frechet_representation (f : H →L[ℝ] ℝ) :
    ∃! u : H, (∀ x : H, f x = ⟪x, u⟫_ℝ) ∧ ‖f‖ = ‖u‖ := by
  refine ⟨(toDual ℝ H).symm f, ?_, ?_⟩
  · constructor
    · intro x
      have hu_apply : toDual ℝ H ((toDual ℝ H).symm f) x = f x := by
        exact DFunLike.congr_fun ((toDual ℝ H).apply_symm_apply f) x
      calc
        f x = toDual ℝ H ((toDual ℝ H).symm f) x := hu_apply.symm
        _ = ⟪x, (toDual ℝ H).symm f⟫_ℝ := by
          rw [toDual_apply_apply, real_inner_comm]
    · exact (((toDual ℝ H).symm).norm_map f).symm
  · intro v hv
    have hv_toDual : toDual ℝ H v = f := by
      ext x
      simpa [toDual_apply_apply, real_inner_comm] using (hv.1 x).symm
    exact (toDual ℝ H).injective <|
      hv_toDual.trans ((toDual ℝ H).apply_symm_apply f).symm

/-! Source item: Chap02/Fact_2_25 -/



variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/- Fact 2.25: on real Hilbert spaces, the adjoint operation is involutive. -/
#check ContinuousLinearMap.adjoint_adjoint

/- Fact 2.25: the orthogonal complement of `ker T` is the closure of `range T†`. -/
#check ContinuousLinearMap.orthogonal_ker

/- Fact 2.25: the orthogonal complement of `range T` is `ker T†`. -/
#check ContinuousLinearMap.orthogonal_range

/- Fact 2.25: `ker (T† ∘L T)` agrees with `ker T`. -/
#check ContinuousLinearMap.ker_adjoint_comp_self

namespace ContinuousLinearMap

/-- Fact 2.25: taking adjoints preserves the operator norm. -/
theorem norm_adjoint_eq (T : H →L[ℝ] K) :
    ‖T†‖ = ‖T‖ := by
  exact LinearIsometryEquiv.norm_map adjoint T

/-- Fact 2.25: the operator norm is the square root of the norm of the Gram operator `T†T`. -/
theorem norm_eq_sqrt_norm_adjoint_comp (T : H →L[ℝ] K) :
    ‖T‖ = Real.sqrt ‖T† ∘L T‖ := by
  calc
    ‖T‖ = Real.sqrt (‖T‖ ^ 2) := by rw [Real.sqrt_sq (norm_nonneg _)]
    _ = Real.sqrt ‖T† ∘L T‖ := by rw [sq, T.norm_adjoint_comp_self]

/-- Fact 2.25: the closures of the ranges of `TT†` and `T` coincide. -/
theorem closure_range_self_comp_adjoint (T : H →L[ℝ] K) :
    (T ∘L T†).range.topologicalClosure = T.range.topologicalClosure := by
  calc
    (T ∘L T†).range.topologicalClosure = ((T ∘L T†).rangeᗮ)ᗮ := by
      rw [Submodule.orthogonal_orthogonal_eq_closure]
    _ = ((T ∘L T†)†.ker)ᗮ := by rw [(T ∘L T†).orthogonal_range]
    _ = ((T ∘L T†).ker)ᗮ := by
      rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
    _ = (T†.ker)ᗮ := by rw [T.ker_self_comp_adjoint]
    _ = T.range.topologicalClosure := by
      rw [T†.orthogonal_ker, ContinuousLinearMap.adjoint_adjoint]

/-- Fact 2.25: in the Hilbert direct sum `H ⊕ K`, the orthogonal complement of the graph of `T`
is the kernel of the canonical graph map `fst + T† ∘ snd`. -/
theorem orthogonal_hilbertGraph (T : H →L[ℝ] K) :
    (T.toLinearMap.graph.map (WithLp.linearEquiv 2 ℝ (H × K)).symm.toLinearMap)ᗮ =
      (WithLp.fstL 2 ℝ H K + T† ∘L WithLp.sndL 2 ℝ H K).ker := by
  ext z
  constructor
  · intro hz
    change (WithLp.fstL 2 ℝ H K + T† ∘L WithLp.sndL 2 ℝ H K) z = 0
    apply ext_inner_right ℝ
    intro x
    have hz' := (Submodule.mem_orthogonal' _ _).mp hz (WithLp.toLp 2 (x, T x))
    have hgraph : WithLp.toLp 2 (x, T x) ∈
        T.toLinearMap.graph.map (WithLp.linearEquiv 2 ℝ (H × K)).symm.toLinearMap := by
      refine Submodule.mem_map.2 ?_
      exact ⟨(x, T x), by simp, rfl⟩
    simpa [WithLp.prod_inner_apply, inner_add_left, T.adjoint_inner_left] using hz' hgraph
  · intro hz
    change (WithLp.fstL 2 ℝ H K + T† ∘L WithLp.sndL 2 ℝ H K) z = 0 at hz
    rw [Submodule.mem_orthogonal']
    intro z hz'
    rcases Submodule.mem_map.1 hz' with ⟨w, hw, rfl⟩
    rw [LinearMap.mem_graph_iff] at hw
    rcases w with ⟨x, y⟩
    have hy : y = T x := by simpa using hw
    have hz0 := congrArg (fun v : H ↦ ⟪v, x⟫_ℝ) hz
    simpa [hy, WithLp.prod_inner_apply, inner_add_left, T.adjoint_inner_left] using hz0

end ContinuousLinearMap

namespace IsSelfAdjoint

/-- For a self-adjoint operator, the norm is the supremum of the quadratic form on the unit ball. -/
theorem norm_eq_sSup_abs_inner_closedBall {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) :
    ‖T‖ = sSup ((fun x : H ↦ |⟪T x, x⟫_ℝ|) '' Metric.closedBall (0 : H) 1) := by
  let s : Set ℝ := (fun x : H ↦ |⟪T x, x⟫_ℝ|) '' Metric.closedBall (0 : H) 1
  have hs_bound : ∀ r ∈ s, r ≤ ‖T‖ := by
    rintro _ ⟨x, hx, rfl⟩
    have hx_norm : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hx_sq : ‖x‖ * ‖x‖ ≤ 1 := by
      nlinarith [norm_nonneg x, hx_norm]
    calc
      |⟪T x, x⟫_ℝ| ≤ ‖T x‖ * ‖x‖ := by
        simpa [Real.norm_eq_abs] using (norm_inner_le_norm (T x) x : ‖⟪T x, x⟫_ℝ‖ ≤ ‖T x‖ * ‖x‖)
      _ ≤ (‖T‖ * ‖x‖) * ‖x‖ := by gcongr; exact le_opNorm T x
      _ = ‖T‖ * (‖x‖ * ‖x‖) := by ring
      _ ≤ ‖T‖ * 1 := by gcongr
      _ = ‖T‖ := by ring
  have hs_bdd : BddAbove s := ⟨‖T‖, hs_bound⟩
  have hs_nonempty : s.Nonempty := by
    refine ⟨0, ?_⟩
    exact ⟨0, by simp, by simp⟩
  refine le_antisymm ?_ ?_
  · change ‖T‖ ≤ sSup s
    exact (Real.le_sSup_iff hs_bdd hs_nonempty).2 fun ε hε ↦ by
      have hlt : ‖T‖ + ε < ⨆ x, |T.rayleighQuotient x| := by
        simpa [T.norm_eq_iSup_rayleighQuotient hT.isSymmetric] using add_lt_add_left hε ‖T‖
      have hlt' : ‖T‖ + ε < sSup (Set.range fun x : H ↦ |T.rayleighQuotient x|) := by
        simpa [sSup_image'] using hlt
      have hs_range_nonempty : (Set.range fun x : H ↦ |T.rayleighQuotient x|).Nonempty := by
        exact ⟨0, ⟨0, by simp⟩⟩
      obtain ⟨r, hr, hrlt⟩ := exists_lt_of_lt_csSup hs_range_nonempty hlt'
      rcases hr with ⟨x, rfl⟩
      by_cases hx : x = 0
      · refine ⟨0, ?_, ?_⟩
        · exact ⟨0, by simp, by simp⟩
        · simpa [hx] using hrlt
      · let y : H := ‖x‖⁻¹ • x
        have hx_norm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
        have hy_norm : ‖y‖ = 1 := by
          calc
            ‖y‖ = ‖x‖⁻¹ * ‖x‖ := by
              simp [y, norm_smul]
            _ = 1 := by field_simp [hx_norm]
        have hy_sphere : y ∈ Metric.sphere (0 : H) 1 := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hy_norm
        have hy_mem : |⟪T y, y⟫_ℝ| ∈ s := by
          refine ⟨y, Metric.sphere_subset_closedBall hy_sphere, rfl⟩
        have hy_rq : T.rayleighQuotient y = ⟪T y, y⟫_ℝ := by
          calc
            T.rayleighQuotient y = T.reApplyInnerSelf y / ‖y‖ ^ 2 := rfl
            _ = T.reApplyInnerSelf y := by simp [hy_norm]
            _ = ⟪T y, y⟫_ℝ := by simpa using hT.isSymmetric.coe_reApplyInnerSelf_apply y
        refine ⟨|⟪T y, y⟫_ℝ|, hy_mem, ?_⟩
        calc
          ‖T‖ + ε < |T.rayleighQuotient x| := hrlt
          _ = |T.rayleighQuotient y| := by
            simpa [y] using congrArg abs (T.rayleigh_smul x (inv_ne_zero hx_norm)).symm
          _ = |⟪T y, y⟫_ℝ| := by rw [hy_rq]
  · change sSup s ≤ ‖T‖
    exact csSup_le hs_nonempty fun r hr ↦ by
      exact hs_bound r hr

end IsSelfAdjoint

/-! Source item: Chap02/Fact_2_28 -/


variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Fact 2.28: the sum `A ⊔ B` is the preimage of the range of the projection onto
`Aᗮ` along `A`. -/
private lemma sup_eq_preimage_range_orthogonalProjection
    {A B : Submodule ℝ H} (hA : IsClosed (A : Set H)) :
    ((A ⊔ B : Submodule ℝ H) : Set H) =
      (let proj : H →L[ℝ] Aᗮ :=
        Aᗮ.orthogonalProjection
      proj ⁻¹' (((proj.comp B.subtypeL : B →ₗ[ℝ] Aᗮ).range : Set Aᗮ))) := by
  let proj : H →L[ℝ] Aᗮ := Aᗮ.orthogonalProjection
  have hAA : Aᗮᗮ ≤ A := by
    intro x hx
    have hx' : x ∈ (⟨A, hA⟩ : ClosedSubmodule ℝ H).toSubmodule := by
      simpa using hx
    simpa using hx'
  ext x
  constructor
  · intro hx
    rcases Submodule.mem_sup.mp hx with ⟨a, ha, b, hb, rfl⟩
    -- Projecting a vector in `A ⊔ B` forgets the `A`-component.
    refine ⟨⟨b, hb⟩, ?_⟩
    change proj b = proj (a + b)
    have hpa : proj a = 0 := by
      exact show Aᗮ.orthogonalProjection a = 0 from
        Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero
          (Submodule.le_orthogonal_orthogonal A ha)
    rw [map_add, hpa, zero_add]
  · intro hx
    rcases hx with ⟨b, hb⟩
    change proj b = proj x at hb
    -- Matching projections means the difference lies in the kernel, hence in `A`.
    have hzero : proj (x - b) = 0 := by
      rw [map_sub, hb, sub_self]
    have hxa : x - b ∈ A := by
      exact hAA <| by
        exact (show Aᗮ.orthogonalProjection (x - b) = 0 ↔ x - b ∈ Aᗮᗮ from
          Submodule.orthogonalProjection_eq_zero_iff).mp <| by
            simpa only [proj] using hzero
    exact Submodule.mem_sup.mpr ⟨x - b, hxa, b, b.property, by abel_nf⟩

/-- If `A` is closed and `B` is finite-dimensional, then `A ⊔ B` is closed. -/
theorem isClosed_sup_of_isClosed_of_finiteDimensional_right
    {A B : Submodule ℝ H} (hA : IsClosed (A : Set H)) [FiniteDimensional ℝ B] :
    IsClosed ((A ⊔ B : Submodule ℝ H) : Set H) := by
  let proj : H →L[ℝ] Aᗮ := Aᗮ.orthogonalProjection
  let f : B →ₗ[ℝ] Aᗮ := proj.comp B.subtypeL
  rw [sup_eq_preimage_range_orthogonalProjection hA]
  -- The projected range is finite-dimensional because it is the image of `B`.
  have hclosed_range : IsClosed ((f.range : Submodule ℝ Aᗮ) : Set Aᗮ) := by
    exact Submodule.closed_of_finiteDimensional f.range
  exact hclosed_range.preimage proj.continuous

/-- If `A` is closed and `Aᗮ` is finite-dimensional, then `B ⊔ A` is closed. -/
theorem isClosed_sup_of_isClosed_of_finiteDimensional_orthogonal_right
    {A B : Submodule ℝ H} (hA : IsClosed (A : Set H)) [FiniteDimensional ℝ Aᗮ] :
    IsClosed ((B ⊔ A : Submodule ℝ H) : Set H) := by
  let proj : H →L[ℝ] Aᗮ := Aᗮ.orthogonalProjection
  let f : B →ₗ[ℝ] Aᗮ := proj.comp B.subtypeL
  rw [sup_comm, sup_eq_preimage_range_orthogonalProjection hA]
  -- Here the projected range is closed because it lies in the finite-dimensional space `Aᗮ`.
  have hclosed_range : IsClosed ((f.range : Submodule ℝ Aᗮ) : Set Aᗮ) := by
    exact Submodule.closed_of_finiteDimensional f.range
  exact hclosed_range.preimage proj.continuous

/-- Fact 2.28: if `U` and `V` are closed linear subspaces of a real Hilbert space and `V` is
finite-dimensional or has finite codimension in the sense that `Vᗮ` is finite-dimensional, then
their sum `U ⊔ V` is closed. -/
-- Proof sketch: in the finite-dimensional case, combine the closedness of `U` with the fact that
-- finite-dimensional subspaces are complete and closed. In the finite-codimensional case, use
-- that `Vᗮ` is finite-dimensional, hence closed, so `V` admits a closed complement and one reduces
-- to the previous case via the orthogonal decomposition associated to `V`.
theorem isClosed_sup_of_isClosed_of_finiteDimensional_or_finiteDimensional_orthogonal
    {U V : Submodule ℝ H} (hU : IsClosed (U : Set H)) (hV : IsClosed (V : Set H))
    (hfinite : FiniteDimensional ℝ V ∨ FiniteDimensional ℝ Vᗮ) :
    IsClosed ((U ⊔ V : Submodule ℝ H) : Set H) := by
  rcases hfinite with hV | hVperp
  · haveI : FiniteDimensional ℝ V := hV
    -- In the first branch, project along the closed subspace `U`.
    exact isClosed_sup_of_isClosed_of_finiteDimensional_right hU
  · haveI : FiniteDimensional ℝ Vᗮ := hVperp
    -- In the finite-codimensional branch, project onto the finite-dimensional complement `Vᗮ`.
    exact isClosed_sup_of_isClosed_of_finiteDimensional_orthogonal_right hV

/-! Source item: Chap02/Definition_2_29 -/


/-- Definition 2.29: for a real or complex Hilbert space `E`, the Hilbert space endowed with its
weak topology is the canonical mathlib type `WeakSpace 𝕜 E`, namely `E` equipped with the coarsest
topology making all continuous linear functionals continuous. -/
-- Proof sketch: use the defining induced-topology characterization of `WeakSpace 𝕜 E`; continuity
-- into the weak topology is equivalent to continuity after composing with every weak evaluation
-- map, and these evaluation maps are exactly `x ↦ l x` for `l : WeakDual 𝕜 E`.
theorem continuous_iff_forall_weakDual_apply
    {𝕜 : Type u} {E : Type v} {α : Type w} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace α] {f : α → WeakSpace 𝕜 E} :
    Continuous f ↔
      ∀ l : WeakDual 𝕜 E, Continuous fun a ↦ l ((toWeakSpace 𝕜 E).symm (f a)) := by
  constructor
  · intro hf l
    simpa only [LinearMap.flip_apply, topDualPairing_apply, toWeakSpace] using
      (WeakBilin.eval_continuous ((topDualPairing 𝕜 E).flip) l).comp hf
  · intro h
    exact WeakBilin.continuous_of_continuous_eval ((topDualPairing 𝕜 E).flip) fun l ↦ by
      simpa only [LinearMap.flip_apply, topDualPairing_apply, toWeakSpace] using h l

/-- For a Hilbert space with its weak topology, each scalar-valued inner-product functional
`x ↦ ⟪x, y⟫` is continuous. -/
-- Proof sketch: transport `x` back to `E` using `(toWeakSpace 𝕜 E).symm`, write the resulting map
-- as scalar conjugation composed with evaluation at `InnerProductSpace.toDual 𝕜 E y`, and then use
-- the defining continuity of evaluations on `WeakSpace 𝕜 E`.
private lemma continuous_inner_right
    {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] (y : E) :
    Continuous fun x : WeakSpace 𝕜 E ↦ inner 𝕜 ((toWeakSpace 𝕜 E).symm x) y := by
  have hEval :
      Continuous fun x : WeakSpace 𝕜 E ↦
        InnerProductSpace.toDual 𝕜 E y ((toWeakSpace 𝕜 E).symm x) := by
    simpa only [LinearMap.flip_apply, topDualPairing_apply, toWeakSpace,
      InnerProductSpace.toDual_apply_apply] using
      WeakBilin.eval_continuous ((topDualPairing 𝕜 E).flip) (InnerProductSpace.toDual 𝕜 E y)
  have hconj :
      Continuous fun x : WeakSpace 𝕜 E ↦
        starRingEnd 𝕜 (InnerProductSpace.toDual 𝕜 E y ((toWeakSpace 𝕜 E).symm x)) :=
    RCLike.continuous_conj.comp hEval
  convert hconj using 1
  ext x
  simp [InnerProductSpace.toDual_apply_apply, inner_conj_symm]

/-- A map into a Hilbert space equipped with its weak topology is continuous exactly when all of
its scalar inner products against fixed vectors are continuous. -/
-- Proof sketch: one direction composes with `weakSpace_continuous_inner_right`; for the converse,
-- recover continuity of all weak evaluation maps via Fréchet-Riesz, expressing each continuous
-- linear functional as `x ↦ conj (⟪x, y⟫)` for a suitable `y`.
theorem continuous_iff_forall_inner_right
    {𝕜 : Type u} {E : Type v} {α : Type w} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] [TopologicalSpace α] {f : α → WeakSpace 𝕜 E} :
    Continuous f ↔
      ∀ y : E, Continuous fun a ↦ inner 𝕜 ((toWeakSpace 𝕜 E).symm (f a)) y := by
  constructor
  · intro hf y
    exact (continuous_inner_right y).comp hf
  · intro h
    rw [continuous_iff_forall_weakDual_apply]
    intro l
    let y : E := (InnerProductSpace.toDual 𝕜 E).symm (WeakDual.toStrongDual l)
    have hy :
        Continuous fun a ↦ inner 𝕜 ((toWeakSpace 𝕜 E).symm (f a)) y :=
      h y
    have hconj :
        Continuous fun a ↦ starRingEnd 𝕜 (inner 𝕜 ((toWeakSpace 𝕜 E).symm (f a)) y) :=
      RCLike.continuous_conj.comp hy
    simpa only [y, WeakDual.toStrongDual_apply, InnerProductSpace.toDual_symm_apply,
      inner_conj_symm] using hconj

/-! Source item: Chap02/Lemma_2_30 -/

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Lemma 2.30: an inner product space equipped with its weak topology is a Hausdorff space.

This is the standard `T2Space (WeakSpace 𝕜 E)` instance specialized to inner product spaces. -/
theorem innerProductSpace_weakSpace_t2Space : T2Space (WeakSpace 𝕜 E) :=
  inferInstance

/-! Source item: Chap03/Proposition_3_27 -/


variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The orthogonal projection of `K` onto the closed range of `T`. -/
noncomputable abbrev closedRangeProjection (T : H →L[ℝ] K)
    (hclosed : IsClosed (T.range : Set K)) : K →L[ℝ] K :=
  letI : CompleteSpace T.range := hclosed.completeSpace_coe
  T.range.starProjection

-- Proof sketch: `closedRangeProjection T hclosed` is the star projection onto the subspace
-- `T.range`, so its values belong to `T.range` by `Submodule.starProjection_apply_mem`.
/-- The orthogonal projection onto the closed range of `T` takes values in `range T`. -/
theorem closedRangeProjection_mem_range (T : H →L[ℝ] K)
    (hclosed : IsClosed (T.range : Set K)) (y : K) :
    closedRangeProjection T hclosed y ∈ T.range := by
  letI : CompleteSpace T.range := hclosed.completeSpace_coe
  simpa [closedRangeProjection] using T.range.starProjection_apply_mem y

/-- The orthogonal projection onto the closed range fixes every point already in the range. -/
theorem closedRangeProjection_eq_self_of_mem_range (T : H →L[ℝ] K)
    (hclosed : IsClosed (T.range : Set K)) {y : K} (hy : y ∈ T.range) :
    closedRangeProjection T hclosed y = y := by
  letI : CompleteSpace T.range := hclosed.completeSpace_coe
  simpa [closedRangeProjection] using (T.range.starProjection_eq_self_iff).2 hy

/-- The orthogonal projection onto the closed range vanishes on the orthogonal complement of that
range. -/
theorem closedRangeProjection_eq_zero_of_mem_orthogonalRange (T : H →L[ℝ] K)
    (hclosed : IsClosed (T.range : Set K)) {y : K} (hy : y ∈ T.rangeᗮ) :
    closedRangeProjection T hclosed y = 0 := by
  letI : CompleteSpace T.range := hclosed.completeSpace_coe
  simpa [closedRangeProjection] using (T.range.starProjection_apply_eq_zero_iff).2 hy

/-- `x` is a least-squares solution of `T z = y` if it minimizes `z ↦ ‖T z - y‖`. -/
abbrev IsLeastSquaresSolution (T : H →L[ℝ] K) (y : K) (x : H) : Prop :=
  ∀ z : H, ‖T x - y‖ ≤ ‖T z - y‖

-- Proof sketch: unfold `IsLeastSquaresSolution`.
/-- The least-squares predicate is the minimization condition for the residual norm. -/
theorem isLeastSquaresSolution_iff (T : H →L[ℝ] K) (y : K) (x : H) :
    IsLeastSquaresSolution T y x ↔ ∀ z : H, ‖T x - y‖ ≤ ‖T z - y‖ := by
  -- This theorem is just the definitional unfolding of `IsLeastSquaresSolution`.
  rfl

/-- Helper for Proposition 3.27: the orthogonal projection onto the closed range agrees with the
metric projection onto `range T`. -/
lemma closedRangeProjection_eq_projectionPoint (T : H →L[ℝ] K)
    (hclosed : IsClosed (T.range : Set K)) (y : K) :
    closedRangeProjection T hclosed y =
      projectionPoint (T.range : Set K)
        (isChebyshev_of_nonempty_isClosed_convex
          (show (T.range : Set K).Nonempty by
            refine ⟨0, ?_⟩
            exact ⟨0, by simp⟩)
          hclosed T.range.convex) y := by
  have hp_mem : closedRangeProjection T hclosed y ∈ (T.range : Set K) := by
    simpa using closedRangeProjection_mem_range T hclosed y
  have horth : y - closedRangeProjection T hclosed y ∈ (T.range : Submodule ℝ K)ᗮ := by
    letI : CompleteSpace T.range := hclosed.completeSpace_coe
    simpa [closedRangeProjection] using T.range.sub_starProjection_mem_orthogonal y
  refine
    (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
      (show (T.range : Set K).Nonempty by
        refine ⟨0, ?_⟩
        exact ⟨0, by simp⟩)
      hclosed T.range.convex).2 ?_
  refine ⟨hp_mem, ?_⟩
  intro r hr
  have hr_sub : r - closedRangeProjection T hclosed y ∈ (T.range : Submodule ℝ K) := by
    exact Submodule.sub_mem T.range hr hp_mem
  have hzero :=
    (Submodule.mem_orthogonal' (T.range : Submodule ℝ K)
      (y - closedRangeProjection T hclosed y)).1 horth
      (r - closedRangeProjection T hclosed y) hr_sub
  simpa [real_inner_comm] using le_of_eq hzero

/-- Helper for Proposition 3.27: minimizing the residual over `H` is equivalent to saying that
`T x` is a best approximation to `y` from `range T`. -/
lemma isLeastSquaresSolution_iff_isBestApproximation_range (T : H →L[ℝ] K)
    (y : K) (x : H) :
    IsLeastSquaresSolution T y x ↔ IsBestApproximation y (T.range : Set K) (T x) := by
  constructor
  · intro hx
    rw [isBestApproximation_iff_mem_and_dist_eq_infDist]
    refine ⟨⟨x, rfl⟩, ?_⟩
    -- The residual at `x` is a lower bound for all residuals coming from the range, and it is
    -- attained at the range point `T x`.
    rw [Metric.infDist_eq_iInf, dist_eq_norm, norm_sub_rev]
    refine le_antisymm ?_ ?_
    · show ‖T x - y‖ ≤ ⨅ r : T.range, dist y (r : K)
      refine le_ciInf ?_
      intro r
      rcases r with ⟨r, ⟨z, rfl⟩⟩
      simpa [dist_eq_norm, norm_sub_rev] using hx z
    · simpa [dist_eq_norm, norm_sub_rev] using
        (ciInf_le
          (show BddBelow (Set.range (fun r : T.range ↦ dist y (r : K))) by
            refine ⟨0, ?_⟩
            rintro _ ⟨r, rfl⟩
            exact dist_nonneg)
          (⟨T x, ⟨x, rfl⟩⟩ : T.range) :
          (⨅ r : T.range, dist y (r : K)) ≤ dist y ((⟨T x, ⟨x, rfl⟩⟩ : T.range) : K))
  · intro hx
    rw [isBestApproximation_iff_mem_and_dist_eq_infDist] at hx
    intro z
    have hle : Metric.infDist y (T.range : Set K) ≤ ‖T z - y‖ := by
      have hdist : Metric.infDist y (T.range : Set K) ≤ dist y (T z) :=
        Metric.infDist_le_dist_of_mem (show T z ∈ (T.range : Set K) by exact ⟨z, rfl⟩)
      simpa [dist_eq_norm, norm_sub_rev] using hdist
    calc
      ‖T x - y‖ = dist y (T x) := by rw [dist_comm, dist_eq_norm]
      _ = Metric.infDist y (T.range : Set K) := hx.2
      _ ≤ ‖T z - y‖ := hle

/-- Helper for Proposition 3.27: a least-squares solution is exactly a point whose image is the
orthogonal projection of `y` onto `range T`. -/
lemma isLeastSquaresSolution_iff_eq_closedRangeProjection (T : H →L[ℝ] K)
    (hclosed : IsClosed (T.range : Set K)) (y : K) (x : H) :
    IsLeastSquaresSolution T y x ↔ T x = closedRangeProjection T hclosed y := by
  let hCheb :=
    isChebyshev_of_nonempty_isClosed_convex
      (show (T.range : Set K).Nonempty by
        refine ⟨0, ?_⟩
        exact ⟨0, by simp⟩)
      hclosed T.range.convex
  constructor
  · intro hx
    have hbest : IsBestApproximation y (T.range : Set K) (T x) :=
      (isLeastSquaresSolution_iff_isBestApproximation_range T y x).1 hx
    -- Uniqueness of best approximations in the closed convex range identifies `T x` with the
    -- canonical projection point.
    have hproj : T x = projectionPoint (T.range : Set K) hCheb y := by
      exact (hCheb y).unique hbest
        (projectionPoint_isBestApproximation (T.range : Set K) hCheb y)
    simpa [closedRangeProjection_eq_projectionPoint T hclosed y] using hproj
  · intro hx
    have hproj : T x = projectionPoint (T.range : Set K) hCheb y := by
      simpa [closedRangeProjection_eq_projectionPoint T hclosed y] using hx
    have hbest : IsBestApproximation y (T.range : Set K) (T x) := by
      simpa [hproj] using
        (projectionPoint_isBestApproximation (T.range : Set K) hCheb y)
    exact (isLeastSquaresSolution_iff_isBestApproximation_range T y x).2 hbest

/-- Helper for Proposition 3.27: the projection identity is equivalent to the normal equation. -/
lemma eq_closedRangeProjection_iff_normal_equation (T : H →L[ℝ] K)
    (hclosed : IsClosed (T.range : Set K)) (y : K) (x : H) :
    T x = closedRangeProjection T hclosed y ↔
      adjoint T (T x) = adjoint T y := by
  constructor
  · intro hx
    have horth : y - T x ∈ (T.range : Submodule ℝ K)ᗮ := by
      letI : CompleteSpace T.range := hclosed.completeSpace_coe
      simpa [hx, closedRangeProjection] using T.range.sub_starProjection_mem_orthogonal y
    have hker : y - T x ∈ (adjoint T).ker := by
      simpa [ContinuousLinearMap.orthogonal_range] using horth
    have hzero : adjoint T (y - T x) = 0 := hker
    have hsub : adjoint T y - adjoint T (T x) = 0 := by
      simpa [ContinuousLinearMap.map_sub] using hzero
    exact (sub_eq_zero.mp hsub).symm
  · intro hEq
    have hsub : adjoint T y - adjoint T (T x) = 0 := by
      rw [hEq, sub_self]
    have hzero : adjoint T (y - T x) = 0 := by
      simpa [ContinuousLinearMap.map_sub] using hsub
    have hker : y - T x ∈ (adjoint T).ker := hzero
    have horth : y - T x ∈ (T.range : Submodule ℝ K)ᗮ := by
      simpa [ContinuousLinearMap.orthogonal_range] using hker
    have hx_mem : T x ∈ (T.range : Submodule ℝ K) := ⟨x, rfl⟩
    letI : CompleteSpace T.range := hclosed.completeSpace_coe
    have hproj :=
      T.range.eq_starProjection_of_mem_orthogonal hx_mem horth
    simpa [closedRangeProjection] using hproj.symm

-- Proof sketch: project `y` orthogonally onto the closed subspace `T.range`, use that the
-- projection point lies in `T.range` to obtain some `x` with `T x = closedRangeProjection T hclosed y`,
-- characterize best approximation in a closed subspace by the orthogonal projection, and rewrite the
-- orthogonality condition by the adjoint identity to obtain the normal equation.
/-- Proposition 3.27: if `range T` is closed, then the least-squares problem
`min_z ‖T z - y‖` admits a solution, and for every `x` the following are equivalent:
`x` is a least-squares solution, `T x` is the orthogonal projection of `y` onto `range T`,
and `T† (T x) = T† y`. -/
theorem leastSquares_tfae_and_exists_of_closed_range (T : H →L[ℝ] K)
    (hclosed : IsClosed (T.range : Set K)) (y : K) :
    (∃ x : H, IsLeastSquaresSolution T y x) ∧
      ∀ x : H, List.TFAE
        [IsLeastSquaresSolution T y x,
          T x = closedRangeProjection T hclosed y,
          adjoint T (T x) = adjoint T y] := by
  refine ⟨?_, ?_⟩
  · rcases closedRangeProjection_mem_range T hclosed y with ⟨x₀, hx₀⟩
    -- A preimage of the closed-range projection provides a least-squares solution.
    refine ⟨x₀, ?_⟩
    exact (isLeastSquaresSolution_iff_eq_closedRangeProjection T hclosed y x₀).2 hx₀
  · intro x
    -- The source proof decomposes the equivalence into the geometric projection criterion and the
    -- normal equation, then closes the three-way equivalence.
    tfae_have 1 ↔ 2 := by
      exact isLeastSquaresSolution_iff_eq_closedRangeProjection T hclosed y x
    tfae_have 2 ↔ 3 := by
      exact eq_closedRangeProjection_iff_normal_equation T hclosed y x
    tfae_finish

/-! Source item: Chap03/Proposition_3_31 -/


variable {𝓗 : Type u} {𝓚 : Type v}
variable [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable [NormedAddCommGroup 𝓚] [InnerProductSpace ℝ 𝓚] [CompleteSpace 𝓚]

/-- A bounded operator `T' : 𝓚 →L[ℝ] 𝓗` is the Moore-Penrose inverse of `T` when each `T' y`
lies in `(ker T)ᗮ` and solves the normal equation `T* T x = T* y`. -/
class IsMoorePenroseInverse (T : 𝓗 →L[ℝ] 𝓚) (T' : 𝓚 →L[ℝ] 𝓗) : Prop where
  mem_orthogonalKer : ∀ y : 𝓚, T' y ∈ T.kerᗮ
  normalEquation : ∀ y : 𝓚, adjoint T (T (T' y)) = adjoint T y

-- Each point in `range T` has a preimage lying in `(ker T)ᗮ`.
omit [CompleteSpace 𝓚] in
private lemma exists_orthogonalKer_preimage_of_mem_range (T : 𝓗 →L[ℝ] 𝓚) {y : 𝓚}
    (hy : y ∈ T.range) :
    ∃ x ∈ T.kerᗮ, T x = y := by
  rcases hy with ⟨x₀, rfl⟩
  refine ⟨x₀ - T.ker.starProjection x₀, ?_, ?_⟩
  · -- Subtracting the kernel projection removes exactly the kernel component.
    exact T.ker.sub_starProjection_mem_orthogonal x₀
  · -- The removed component lies in `ker T`, so `T` does not change.
    have hk_mem : T.ker.starProjection x₀ ∈ T.ker := by
      exact Submodule.starProjection_apply_mem T.ker x₀
    have hk_zero : T (T.ker.starProjection x₀) = 0 := by
      exact (LinearMap.mem_ker).1 hk_mem
    simpa [map_sub, hk_zero]

-- Under the Moore-Penrose normal equation, `T ∘L T'` is the orthogonal projection onto
-- `range T`.
private lemma comp_apply_eq_closedRangeProjection_of_isMoorePenroseInverse
    (T : 𝓗 →L[ℝ] 𝓚) (T' : 𝓚 →L[ℝ] 𝓗)
    (hT_closed : IsClosed (T.range : Set 𝓚))
    (hmp : IsMoorePenroseInverse T T') (y : 𝓚) :
    T (T' y) = closedRangeProjection T hT_closed y := by
  -- The normal equation is exactly the characterization of the closed-range projection.
  exact
    (eq_closedRangeProjection_iff_normal_equation T hT_closed y (T' y)).2 (hmp.normalEquation y)

-- The projection conditions force `ker T` to be the orthogonal complement of `range T'`.
private lemma ker_eq_orthogonal_tilde_range_of_projection_conditions
    (T : 𝓗 →L[ℝ] 𝓚) (T' : 𝓚 →L[ℝ] 𝓗)
    (hT_closed : IsClosed (T.range : Set 𝓚))
    (hT'_closed : IsClosed (T'.range : Set 𝓗))
    (hproj : T ∘L T' = closedRangeProjection T hT_closed ∧
      T' ∘L T = closedRangeProjection T' hT'_closed) :
    T.ker = T'.rangeᗮ := by
  ext x
  constructor
  · intro hx
    -- Kernel vectors are annihilated by the projector onto `range T'`, hence lie in its
    -- orthogonal complement.
    let S : Submodule ℝ 𝓗 := T'.range
    have hzero : closedRangeProjection T' hT'_closed x = 0 := by
      have hrev :=
        congrArg (fun f : 𝓗 →L[ℝ] 𝓗 ↦ f x) hproj.2
      have hx_zero : T x = 0 := (LinearMap.mem_ker).1 hx
      calc
        closedRangeProjection T' hT'_closed x = T' (T x) := by simpa using hrev.symm
        _ = 0 := by simp [hx_zero]
    simpa [S, closedRangeProjection] using
      (show S.starProjection x = 0 ↔ x ∈ Sᗮ from S.starProjection_apply_eq_zero_iff).1 hzero
  · intro hx
    -- Conversely, if the projector onto `range T'` kills `x`, then `T' (T x) = 0`.
    let S : Submodule ℝ 𝓗 := T'.range
    have hzero' : T' (T x) = 0 := by
      have hz : closedRangeProjection T' hT'_closed x = 0 := by
        simpa [S, closedRangeProjection] using
          (show S.starProjection x = 0 ↔ x ∈ Sᗮ from S.starProjection_apply_eq_zero_iff).2 hx
      have hrev :=
        congrArg (fun f : 𝓗 →L[ℝ] 𝓗 ↦ f x) hproj.2
      exact hrev.trans hz
    -- Evaluating `T ∘L T' = P_{range T}` at `T x` gives the identity `T x = T (T' (T x))`.
    have hTx : T x = T (T' (T x)) := by
      have hcomp :=
        congrArg (fun f : 𝓚 →L[ℝ] 𝓚 ↦ f (T x)) hproj.1
      have hself : closedRangeProjection T hT_closed (T x) = T x := by
        exact closedRangeProjection_eq_self_of_mem_range T hT_closed ⟨x, rfl⟩
      simpa [hself] using hcomp.symm
    have hx_zero : T x = 0 := by
      simpa [hzero'] using hTx
    exact (LinearMap.mem_ker).2 hx_zero

-- Under the projection conditions, `range T'` is exactly `(ker T)ᗮ`.
private lemma range_eq_orthogonal_ker_of_projection_conditions
    (T : 𝓗 →L[ℝ] 𝓚) (T' : 𝓚 →L[ℝ] 𝓗)
    (hT_closed : IsClosed (T.range : Set 𝓚))
    (hT'_closed : IsClosed (T'.range : Set 𝓗))
    (hproj : T ∘L T' = closedRangeProjection T hT_closed ∧
      T' ∘L T = closedRangeProjection T' hT'_closed) :
    T'.range = T.kerᗮ := by
  have hker :
      T.ker = T'.rangeᗮ :=
    ker_eq_orthogonal_tilde_range_of_projection_conditions T T' hT_closed hT'_closed hproj
  ext x
  constructor
  · intro hx
    -- Every vector in `range T'` lies in the double orthogonal of `range T'`.
    rw [hker]
    exact Submodule.le_orthogonal_orthogonal (T'.range : Submodule ℝ 𝓗) hx
  · intro hx
    -- Closedness of `range T'` identifies its double orthogonal with itself.
    rw [hker] at hx
    have hclosure : (T'.range : Submodule ℝ 𝓗).topologicalClosure = T'.range := by
      exact IsClosed.submodule_topologicalClosure_eq hT'_closed
    have hx' : x ∈ (T'.range : Submodule ℝ 𝓗).topologicalClosure := by
      simpa [Submodule.orthogonal_orthogonal_eq_closure, hclosure] using hx
    simpa [hclosure] using hx'

-- Proof sketch: `(i) → (ii)` uses the defining projection identities for a Moore-Penrose inverse;
-- `(ii) → (iii)` combines those projection equalities with the orthogonal decompositions along
-- `T.kerᗮ` and `T.rangeᗮ`; `(iii) → (i)` decomposes each `y` into its `range T` and `range Tᗮ`
-- components and uses the normal-equation characterization in `IsMoorePenroseInverse`.
/-- Proposition 3.31: for bounded operators `T : 𝓗 →L[ℝ] 𝓚` and `T' : 𝓚 →L[ℝ] 𝓗` with closed
ranges, the following are equivalent: (i) `T'` is the Moore-Penrose inverse of `T`; (ii)
`T ∘L T'` and `T' ∘L T` are the orthogonal projections onto `range T` and `range T'`; (iii)
`T' ∘L T` is the identity on `T.kerᗮ` and `T'` vanishes on `T.rangeᗮ`. -/
theorem isMoorePenroseInverse_tfae_projection_and_orthogonal_conditions
    (T : 𝓗 →L[ℝ] 𝓚) (T' : 𝓚 →L[ℝ] 𝓗)
    (hT_closed : IsClosed (T.range : Set 𝓚))
    (hT'_closed : IsClosed (T'.range : Set 𝓗)) :
    List.TFAE
      [IsMoorePenroseInverse T T',
        T ∘L T' = closedRangeProjection T hT_closed ∧
          T' ∘L T = closedRangeProjection T' hT'_closed,
        (∀ x ∈ T.kerᗮ, T' (T x) = x) ∧
          ∀ y ∈ T.rangeᗮ, T' y = 0] := by
  -- The source proof runs through the projection identities, then identifies the relevant
  -- orthogonal complements, and finally reconstructs the normal equation from the projection.
  tfae_have 1 → 2 := by
    intro hmp
    refine ⟨?_, ?_⟩
    · -- Clause `(i) → (ii)`, first projection identity: the normal equation identifies
      -- `T (T' y)` with the orthogonal projection of `y` onto `range T`.
      ext y
      exact comp_apply_eq_closedRangeProjection_of_isMoorePenroseInverse T T' hT_closed hmp y
    · -- Clause `(i) → (ii)`, second projection identity: `T' (T x)` is the orthogonal
      -- projection of `x` onto `range T'`.
      ext x
      have hker_mem : x - T' (T x) ∈ T.ker := by
        have hcompTx :
            T (T' (T x)) = closedRangeProjection T hT_closed (T x) := by
          exact comp_apply_eq_closedRangeProjection_of_isMoorePenroseInverse T T' hT_closed hmp
            (T x)
        have hself : closedRangeProjection T hT_closed (T x) = T x := by
          exact closedRangeProjection_eq_self_of_mem_range T hT_closed ⟨x, rfl⟩
        have hzero : T (x - T' (T x)) = 0 := by
          simpa [map_sub, hself] using congrArg (fun z : 𝓚 ↦ T x - z) hcompTx
        exact (LinearMap.mem_ker).2 hzero
      have hker_orth : x - T' (T x) ∈ T.kerᗮᗮ := by
        exact Submodule.le_orthogonal_orthogonal T.ker hker_mem
      have horth : x - T' (T x) ∈ (T'.range : Submodule ℝ 𝓗)ᗮ := by
        rw [Submodule.mem_orthogonal']
        intro z hz
        rcases hz with ⟨y, rfl⟩
        exact
          (Submodule.mem_orthogonal' (T.kerᗮ) (x - T' (T x))).1 hker_orth
            (T' y) (hmp.mem_orthogonalKer y)
      have hmem : T' (T x) ∈ (T'.range : Submodule ℝ 𝓗) := by
        exact ⟨T x, rfl⟩
      let S : Submodule ℝ 𝓗 := T'.range
      have hproj' : S.starProjection x = T' (T x) := by
        simpa [S] using S.eq_starProjection_of_mem_orthogonal hmem horth
      simpa [S, closedRangeProjection] using hproj'.symm
  tfae_have 2 → 3 := by
    intro hproj
    refine ⟨?_, ?_⟩
    · -- Clause `(ii) → (iii)`: identify `range T'` with `(ker T)ᗮ`, then the projector acts as
      -- the identity there.
      intro x hx
      have hrange : T'.range = T.kerᗮ :=
        range_eq_orthogonal_ker_of_projection_conditions T T' hT_closed hT'_closed hproj
      have hx_range : x ∈ T'.range := by
        simpa [hrange] using hx
      have hself : closedRangeProjection T' hT'_closed x = x := by
        exact closedRangeProjection_eq_self_of_mem_range T' hT'_closed hx_range
      have hrev :=
        congrArg (fun f : 𝓗 →L[ℝ] 𝓗 ↦ f x) hproj.2
      simpa [hself] using hrev
    · -- Clause `(ii) → (iii)`: factor `T'` through the projection onto `range T`.
      intro y hy
      have hy_mem : T' y ∈ T'.range := by
        exact ⟨y, rfl⟩
      have hself' : closedRangeProjection T' hT'_closed (T' y) = T' y := by
        exact closedRangeProjection_eq_self_of_mem_range T' hT'_closed hy_mem
      have hrev :=
        congrArg (fun f : 𝓗 →L[ℝ] 𝓗 ↦ f (T' y)) hproj.2
      have hcomp :=
        congrArg (fun f : 𝓚 →L[ℝ] 𝓚 ↦ f y) hproj.1
      have hcomp' : T (T' y) = closedRangeProjection T hT_closed y := by
        simpa using hcomp
      have hfactor : T' y = T' (closedRangeProjection T hT_closed y) := by
        calc
          T' y = T' (T (T' y)) := by
            simpa [hself'] using hrev.symm
          _ = T' (closedRangeProjection T hT_closed y) := by
            rw [hcomp']
      rw [hfactor, closedRangeProjection_eq_zero_of_mem_orthogonalRange T hT_closed hy, map_zero]
  tfae_have 3 → 1 := by
    intro horth
    have hy : ∀ y : 𝓚,
        T' y ∈ T.kerᗮ ∧ adjoint T (T (T' y)) = adjoint T y := by
      intro y
      let p := closedRangeProjection T hT_closed y
      let S : Submodule ℝ 𝓚 := T.range
      have hp_mem : p ∈ T.range := by
        exact closedRangeProjection_mem_range T hT_closed y
      have hres : y - p ∈ T.rangeᗮ := by
        -- The residual from the orthogonal projection lies in the orthogonal complement of
        -- `range T`.
        simpa [p, closedRangeProjection] using S.sub_starProjection_mem_orthogonal y
      rcases exists_orthogonalKer_preimage_of_mem_range T hp_mem with ⟨x₁, hx₁_orth, hx₁_eq⟩
      have hTp : T' p = x₁ := by
        -- On `(ker T)ᗮ`, the composition `T' ∘L T` is the identity.
        simpa [hx₁_eq] using horth.1 x₁ hx₁_orth
      have hTr : T' (y - p) = 0 := by
        -- On `range Tᗮ`, the operator `T'` vanishes.
        exact horth.2 (y - p) hres
      have hpdecomp : p + (y - p) = y := by
        simp [sub_eq_add_neg, add_left_comm]
      have hsplit : T' y = x₁ := by
        -- Decompose `y` into its projected and orthogonal components and apply the two clauses of
        -- condition `(iii)`.
        calc
          T' y = T' (p + (y - p)) := by rw [hpdecomp]
          _ = T' p + T' (y - p) := by rw [map_add]
          _ = x₁ + 0 := by rw [hTp, hTr]
          _ = x₁ := by simp
      have hproj : T (T' y) = p := by
        simpa [hsplit] using hx₁_eq
      refine ⟨?_, ?_⟩
      · -- The decomposition shows `T' y` lies in `(ker T)ᗮ`.
        simpa [hsplit] using hx₁_orth
      · -- The projection identity recovers the normal equation.
        exact
          (eq_closedRangeProjection_iff_normal_equation T hT_closed y (T' y)).1
            (by simpa [p] using hproj)
    refine ⟨?_, ?_⟩
    · intro y
      exact (hy y).1
    · intro y
      exact (hy y).2
  tfae_finish

/-! Source item: Chap03/Example_3_29 -/


variable {𝓗 : Type u} {𝓚 : Type v}
variable [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable [NormedAddCommGroup 𝓚] [InnerProductSpace ℝ 𝓚] [CompleteSpace 𝓚]

private noncomputable abbrev normalEquationInverseCompAdjoint (T : 𝓗 →L[ℝ] 𝓚) :
    𝓚 →L[ℝ] 𝓗 :=
  (T.adjoint ∘L T).inverse ∘L T.adjoint

private lemma normalOperator_ker_eq_bot (T : 𝓗 →L[ℝ] 𝓚)
    [Fact (IsUnit (T.adjoint ∘L T))] :
    (T.adjoint ∘L T).ker = ⊥ := by
  refine LinearMap.ker_eq_bot'.2 ?_
  intro x hx
  have hcancel :
      (T.adjoint ∘L T).inverse ((T.adjoint ∘L T) x) = x := by
    simpa [← ringInverse_eq_inverse, one_def] using
      congrArg (fun A : 𝓗 →L[ℝ] 𝓗 ↦ A x)
        (Ring.inverse_mul_cancel (T.adjoint ∘L T) (Fact.out : IsUnit (T.adjoint ∘L T)))
  calc
    x = (T.adjoint ∘L T).inverse ((T.adjoint ∘L T) x) := by simpa using hcancel.symm
    _ = (T.adjoint ∘L T).inverse 0 := by
      exact congrArg ((T.adjoint ∘L T).inverse) hx
    _ = 0 := by simp

private lemma ker_eq_bot_of_isUnit_normalOperator (T : 𝓗 →L[ℝ] 𝓚)
    [Fact (IsUnit (T.adjoint ∘L T))] :
    T.ker = ⊥ := by
  rw [← ContinuousLinearMap.ker_adjoint_comp_self]
  exact normalOperator_ker_eq_bot T

private lemma normalEquationPseudoinverse_mem_orthogonalKer (T : 𝓗 →L[ℝ] 𝓚)
    [Fact (IsUnit (T.adjoint ∘L T))] (y : 𝓚) :
    normalEquationInverseCompAdjoint T y ∈ T.kerᗮ := by
  rw [ker_eq_bot_of_isUnit_normalOperator T]
  simp

-- Proof sketch: invertibility of `T†T` forces `ker T = ⊥`, so the orthogonality condition in
-- `IsMoorePenroseInverse` is automatic; the normal equation is the cancellation identity
-- `(T†T) (T†T)⁻¹ T† = T†`.
/-- Example 3.29: if `T†T` is invertible, then the operator `(T†T)⁻¹ T†` is the Moore-Penrose
inverse of `T`. -/
theorem normalEquationPseudoinverse_isMoorePenroseInverse
    (T : 𝓗 →L[ℝ] 𝓚) [Fact (IsUnit (T.adjoint ∘L T))] :
    IsMoorePenroseInverse T ((T.adjoint ∘L T).inverse ∘L T.adjoint) := by
  refine ⟨?_, ?_⟩
  · exact normalEquationPseudoinverse_mem_orthogonalKer T
  · intro y
    have hcomp :
        (T.adjoint ∘L T) ∘L normalEquationInverseCompAdjoint T = T.adjoint := by
      simpa [normalEquationInverseCompAdjoint, ContinuousLinearMap.comp_assoc,
        ← ringInverse_eq_inverse, one_def]
        using
          congrArg (fun A : 𝓗 →L[ℝ] 𝓗 ↦ A ∘L T.adjoint)
            (Ring.mul_inverse_cancel (T.adjoint ∘L T) (Fact.out : IsUnit (T.adjoint ∘L T)))
    simpa using congrArg (fun A : 𝓚 →L[ℝ] 𝓗 ↦ A y) hcomp

/-- The normal-equation pseudoinverse can be used through typeclass search when `T†T` is
invertible. -/
instance (T : 𝓗 →L[ℝ] 𝓚) [Fact (IsUnit (T.adjoint ∘L T))] :
    IsMoorePenroseInverse T ((T.adjoint ∘L T).inverse ∘L T.adjoint) :=
  normalEquationPseudoinverse_isMoorePenroseInverse T
