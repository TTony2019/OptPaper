import Mathlib
import Mathlib.Data.List.TFAE
import Foundation.FixedPoint.Nonexpansive
import Foundation.Hilbert.Basic

/-!
# FixedPoint Averaged

Averaged mappings, relaxation transforms, averaged compositions, and relationships with firm nonexpansiveness and cocoercivity.
-/

open Set
open scoped BigOperators

/-! Source item: Chap04/Definition_4_33 -/
universe u

section

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {D : Set H}

/-- Definition 4.33: a map `T : D → H` is averaged with constant `α` when `α ∈ ]0, 1[` and
there is a nonexpansive map `R : D → H` such that `T = (1 - α) Id + α R`. -/
def AveragedWith (α : ℝ) (T : D → H) : Prop :=
  α ∈ Set.Ioo (0 : ℝ) 1 ∧
    ∃ R : D → H, LipschitzWith 1 R ∧
      T = fun x : D ↦ (1 - α) • (x : H) + α • R x

/-- An `α`-averaged map has averaging parameter `α ∈ ]0, 1[`. -/
theorem AveragedWith.mem_Ioo {α : ℝ} {T : D → H} (hT : AveragedWith α T) :
    α ∈ Set.Ioo (0 : ℝ) 1 :=
  hT.1

-- Proof sketch: unfold `AveragedWith`.
/-- A map is `α`-averaged exactly when `α ∈ ]0, 1[` and it is the affine combination of the
identity on `D` with a nonexpansive companion map. -/
theorem averagedWith_iff {α : ℝ} {T : D → H} :
    AveragedWith α T ↔
      α ∈ Set.Ioo (0 : ℝ) 1 ∧
        ∃ R : D → H, LipschitzWith 1 R ∧
          T = fun x : D ↦ (1 - α) • (x : H) + α • R x := by
  rfl

end

/-! Source item: Abbas 2015 Definition 3.1 (whole-space α-averaged operators) -/

section

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- An `α`-averaged operator on the whole space: `T = (1 - α) Id + α R` with a nonexpansive
companion `R` (Definition 3.1 of Abbas 2015); the canonical set-domain version is
`AveragedWith`. -/
def IsAveragedOperator (T : H → H) (alpha : ℝ) (_halpha : 0 < alpha ∧ alpha < 1) : Prop :=
  AveragedWith alpha (fun x : (Set.univ : Set H) ↦ T x)

/-- The whole-space and set-domain formulations of averagedness coincide on the full set. -/
theorem isAveragedOperator_iff_averagedWith (T : H → H) (alpha : ℝ)
    (halpha : 0 < alpha ∧ alpha < 1) :
    IsAveragedOperator T alpha halpha ↔
      AveragedWith alpha (fun x : (Set.univ : Set H) ↦ T x) := by
  rfl

end

/-! Source item: Chap04/Remark_4_34 -/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Remark 4.34 (1): every averaged map on a subset of a real Hilbert space is nonexpansive. -/
theorem lipschitzWith_one_of_averagedWith {D : Set H} {α : ℝ} {T : D → H}
    (hT : AveragedWith α T) : LipschitzWith 1 T := by
  rcases averagedWith_iff.mp hT with ⟨hα, R, hR, hT_eq⟩
  have hα_nonneg : 0 ≤ α := hα.1.le
  have h_one_sub_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα.2.le
  -- Control the averaged companion by the given nonexpansive witness.
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have hRxy : ‖R x - R y‖ ≤ ‖(x : H) - y‖ := by
    simpa [Subtype.dist_eq, dist_eq_norm] using hR.dist_le_mul x y
  have hxy :
      T x - T y = (1 - α) • ((x : H) - y) + α • (R x - R y) := by
    -- Rewrite the affine representation pointwise and collect the two differences.
    calc
      T x - T y
          = ((1 - α) • (x : H) + α • R x) - ((1 - α) • (y : H) + α • R y) := by
              rw [hT_eq]
      _ = (1 - α) • ((x : H) - y) + α • (R x - R y) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- The triangle inequality and the witness bound collapse the convex combination to `‖x - y‖`.
  simpa [Subtype.dist_eq, dist_eq_norm, one_mul] using
    calc
      ‖T x - T y‖ = ‖(1 - α) • ((x : H) - y) + α • (R x - R y)‖ := by rw [hxy]
      _ ≤ ‖(1 - α) • ((x : H) - y)‖ + ‖α • (R x - R y)‖ := norm_add_le _ _
      _ = (1 - α) * ‖(x : H) - y‖ + α * ‖R x - R y‖ := by
            rw [norm_smul, norm_smul]
            simp [Real.norm_eq_abs, abs_of_nonneg h_one_sub_nonneg, abs_of_nonneg hα_nonneg]
      _ ≤ (1 - α) * ‖(x : H) - y‖ + α * ‖(x : H) - y‖ := by
            nlinarith [hRxy, norm_nonneg ((x : H) - y)]
      _ = ‖(x : H) - y‖ := by ring

/-- Helper for Remark 4.34: `1 / 2`-averagedness is exactly nonexpansiveness of the reflected
map `2T - Id`. -/
private lemma averagedWith_half_iff_reflectedMap_pairwise_nonexpansive {D : Set H} (T : D → H) :
    AveragedWith (1 / 2 : ℝ) T ↔
      ∀ x y : D, ‖reflectedMap D T x - reflectedMap D T y‖ ≤ ‖(x : H) - y‖ := by
  constructor
  · intro hT
    rcases averagedWith_iff.mp hT with ⟨hhalf, R, hR, hT_eq⟩
    intro x y
    have hreflect_eq : reflectedMap D T = R := by
      -- For the special weight `1 / 2`, the averaged companion is exactly the reflector `2T - Id`.
      funext z
      calc
        reflectedMap D T z = (2 : ℝ) • T z - z := rfl
        _ = (2 : ℝ) • ((1 - (1 / 2 : ℝ)) • (z : H) + (1 / 2 : ℝ) • R z) - z := by
              rw [hT_eq]
        _ = R z := by
              have hhalf_eq : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by norm_num
              rw [hhalf_eq, smul_add, smul_smul, smul_smul]
              norm_num
    -- After identifying the reflector with `R`, reuse the original nonexpansive witness.
    simpa [hreflect_eq, Subtype.dist_eq, dist_eq_norm] using hR.dist_le_mul x y
  · intro hT
    have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
      norm_num
    have hR : LipschitzWith 1 (reflectedMap D T) := by
      -- Convert the pairwise norm estimate into the standard Lipschitz form on the subtype domain.
      refine LipschitzWith.of_dist_le_mul ?_
      intro x y
      simpa [Subtype.dist_eq, dist_eq_norm, one_mul] using hT x y
    refine averagedWith_iff.mpr ⟨hhalf, reflectedMap D T, hR, ?_⟩
    -- Reconstruct the averaged decomposition from the explicit reflected map formula.
    funext x
    have hsmul : (1 / 2 : ℝ) • ((2 : ℝ) • T x) = T x := by
      rw [smul_smul]
      norm_num
    calc
      T x = (1 / 2 : ℝ) • ((2 : ℝ) • T x) := by rw [hsmul]
      _ = (1 - (1 / 2 : ℝ)) • (x : H) + (1 / 2 : ℝ) • reflectedMap D T x := by
            rw [reflectedMap, smul_sub, hsmul]
            norm_num

/-- Remark 4.34 (2): a map on a subset of a real Hilbert space is firmly nonexpansive if and
only if it is `1 / 2`-averaged. -/
theorem firmlyNonexpansiveOn_iff_averagedWith_half {D : Set H} (T : D → H) :
    FirmlyNonexpansiveOn D T ↔ AveragedWith (1 / 2 : ℝ) T := by
  -- Route correction: use the earlier reflector criterion from Proposition 4.4 rather than the
  -- later TFAE package for averaged maps.
  calc
    FirmlyNonexpansiveOn D T ↔
        ∀ x y : D, ‖reflectedMap D T x - reflectedMap D T y‖ ≤ ‖(x : H) - y‖ := by
          exact (reflectedMap_nonexpansive_iff_firmlyNonexpansiveOn D T).symm
    _ ↔ AveragedWith (1 / 2 : ℝ) T := by
      exact averagedWith_half_iff_reflectedMap_pairwise_nonexpansive T |>.symm

/-- Helper for Remark 4.34(3): scaling by a positive scalar turns cocoercivity into firm
nonexpansiveness. -/
private lemma cocoerciveOn_iff_firmlyNonexpansiveOn_smul {D : Set H} {β : ℝ} (hβ : 0 < β)
    (T : D → H) :
    CocoerciveOn β D T ↔ FirmlyNonexpansiveOn D (fun x : D ↦ β • T x) := by
  rw [CocoerciveOn, firmlyNonexpansiveOn_iff]
  constructor
  · rintro ⟨_, hT⟩ x y
    -- Multiply the cocoercive inequality by `β` and rewrite the scaled norm and inner product.
    have hscaled :
        β * (β * ‖T x - T y‖ ^ 2) ≤ β * inner ℝ ((x : H) - y) (T x - T y) := by
      exact mul_le_mul_of_nonneg_left (hT x y) hβ.le
    have hnorm :
        ‖β • T x - β • T y‖ ^ 2 = β * (β * ‖T x - T y‖ ^ 2) := by
      calc
        ‖β • T x - β • T y‖ ^ 2 = ‖β • (T x - T y)‖ ^ 2 := by rw [smul_sub]
        _ = (β * ‖T x - T y‖) ^ 2 := by
              simp [norm_smul, abs_of_nonneg hβ.le]
        _ = β * (β * ‖T x - T y‖ ^ 2) := by
              rw [pow_two]
              ring
    have hinner :
        inner ℝ ((x : H) - y) (β • T x - β • T y) =
          β * inner ℝ ((x : H) - y) (T x - T y) := by
      rw [← smul_sub, real_inner_smul_right]
    rw [hnorm, hinner]
    exact hscaled
  · intro hT
    refine ⟨hβ, ?_⟩
    intro x y
    -- The same identities run backwards, and positivity of `β` lets `nlinarith` divide it out.
    have hscaled := hT x y
    have hnorm :
        ‖β • T x - β • T y‖ ^ 2 = β * (β * ‖T x - T y‖ ^ 2) := by
      calc
        ‖β • T x - β • T y‖ ^ 2 = ‖β • (T x - T y)‖ ^ 2 := by rw [smul_sub]
        _ = (β * ‖T x - T y‖) ^ 2 := by
              simp [norm_smul, abs_of_nonneg hβ.le]
        _ = β * (β * ‖T x - T y‖ ^ 2) := by
              rw [pow_two]
              ring
    have hinner :
        inner ℝ ((x : H) - y) (β • T x - β • T y) =
          β * inner ℝ ((x : H) - y) (T x - T y) := by
      rw [← smul_sub, real_inner_smul_right]
    rw [hnorm, hinner] at hscaled
    nlinarith

/-- Remark 4.34 (3): for `β > 0`, a map on a subset of a real Hilbert space is `β`-cocoercive if
and only if the scaled map `x ↦ β • T x` is `1 / 2`-averaged. -/
theorem cocoerciveOn_iff_smul_averagedWith_half {D : Set H} {β : ℝ} (hβ : 0 < β) (T : D → H) :
    CocoerciveOn β D T ↔ AveragedWith (1 / 2 : ℝ) (fun x : D ↦ β • T x) := by
  -- Normalize to firm nonexpansiveness after scaling, then apply the half-averaged criterion.
  calc
    CocoerciveOn β D T ↔ FirmlyNonexpansiveOn D (fun x : D ↦ β • T x) := by
      exact cocoerciveOn_iff_firmlyNonexpansiveOn_smul hβ T
    _ ↔ AveragedWith (1 / 2 : ℝ) (fun x : D ↦ β • T x) := by
      exact firmlyNonexpansiveOn_iff_averagedWith_half (fun x : D ↦ β • T x)

/-! Source item: Chap04/Proposition_4_35 -/

section

variable {H : Type u} [NormedAddCommGroup H]
variable {D : Set H}

/-- Helper for Proposition 4.35: on a subtype domain, `LipschitzWith 1` is equivalent to the
pairwise nonexpansive norm inequality. -/
-- Proof sketch: rewrite the metric Lipschitz estimate using `Subtype.dist_eq` and `dist_eq_norm`.
private lemma lipschitzWith_one_iff_pairwise_norm_sub_le {T : D → H} :
    LipschitzWith 1 T ↔ ∀ x y : D, ‖T x - T y‖ ≤ ‖(x : H) - y‖ := by
  constructor
  · intro hT x y
    -- Convert the ambient metric bound into the norm estimate on `H`.
    simpa [Subtype.dist_eq, dist_eq_norm] using hT.dist_le_mul x y
  · intro hT
    -- Repackage the pointwise norm control as a Lipschitz estimate.
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simpa [Subtype.dist_eq, dist_eq_norm] using hT x y

/-- Helper for Proposition 4.35: comparing the squared norms of two vectors is equivalent to
comparing their norms. -/
-- Proof sketch: use `sq_le_sq` and the nonnegativity of norms to remove absolute values.
private lemma norm_sq_le_norm_sq_iff {x y : H} : ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 ↔ ‖x‖ ≤ ‖y‖ := by
  constructor
  · intro h
    have hsq := sq_le_sq.mp h
    -- Norms are nonnegative, so the square comparison reduces to the usual order comparison.
    simpa [abs_of_nonneg (norm_nonneg x), abs_of_nonneg (norm_nonneg y)] using hsq
  · intro h
    -- Squaring preserves the inequality because both norms are nonnegative.
    exact sq_le_sq.mpr <| by
      simpa [abs_of_nonneg (norm_nonneg x), abs_of_nonneg (norm_nonneg y)] using h

/-- Helper for Proposition 4.35: the residual difference `((Id - T) x) - ((Id - T) y)` is
`(x - y) - (T x - T y)`. -/
-- Proof sketch: expand both subtractions and reassociate the resulting sum.
private lemma residual_difference_eq {T : D → H} (x y : D) :
    ((x : H) - T x) - (y - T y) = ((x : H) - y) - (T x - T y) := by
  -- This is the canonical regrouping of the residual terms.
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

end

section

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {D : Set H}

/-- Helper for Proposition 4.35: subtracting the affine transform at two points produces the
expected affine combination of the input and output differences. -/
-- Proof sketch: expand the subtraction and regroup the two scalar multiples separately.
private lemma averaging_transform_sub {α : ℝ} {T : D → H} (x y : D) :
    ((1 - 1 / α) • (x : H) + (1 / α) • T x) -
        ((1 - 1 / α) • (y : H) + (1 / α) • T y) =
      (1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y) := by
  -- Both sides are the same affine difference after distributing subtraction over addition.
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_add]

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {D : Set H}

/-- Helper for Proposition 4.35: the affine transform is nonexpansive exactly when the residual
quadratic inequality from clause (3) holds. -/
-- Proof sketch: translate nonexpansiveness into a squared norm comparison, apply the identity from
-- Lemma 2.17, and divide by the positive scalar `α`.
private theorem averaging_transform_lipschitz_iff_residual_ineq
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {T : D → H} :
    LipschitzWith 1 (fun x : D ↦ (1 - 1 / α) • (x : H) + (1 / α) • T x) ↔
      ∀ x y : D,
        ‖T x - T y‖ ^ 2 ≤
          ‖(x : H) - y‖ ^ 2 -
            ((1 - α) / α) * ‖((x : H) - T x) - (y - T y)‖ ^ 2 := by
  rw [lipschitzWith_one_iff_pairwise_norm_sub_le]
  constructor
  · intro hS x y
    -- First square the nonexpansive estimate for the affine transform.
    have hSxy := hS x y
    rw [averaging_transform_sub] at hSxy
    have hsq :
        ‖(1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y)‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2 := by
      exact (norm_sq_le_norm_sq_iff).2 hSxy
    have hnonneg :
        0 ≤ α ^ 2 *
          (‖(x : H) - y‖ ^ 2 -
            ‖(1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y)‖ ^ 2) := by
      -- Multiplying by the positive factor `α^2` preserves nonnegativity.
      nlinarith [hsq, hα.1]
    have hrewrite :
        0 ≤ α *
          (‖(x : H) - y‖ ^ 2 -
            α⁻¹ * (1 - α) * ‖((x : H) - y) - (T x - T y)‖ ^ 2 -
              ‖T x - T y‖ ^ 2) := by
      -- Lemma 2.17 rewrites the scaled squared-norm gap into the residual expression.
      rwa [alpha_sq_norm_sq_sub_inv_affine_combination_eq_norm_sub
        ((x : H) - y) (T x - T y) hα] at hnonneg
    have hgap :
        0 ≤ ‖(x : H) - y‖ ^ 2 -
          α⁻¹ * (1 - α) * ‖((x : H) - y) - (T x - T y)‖ ^ 2 -
            ‖T x - T y‖ ^ 2 := by
      -- Divide by the positive scalar `α`.
      nlinarith [hrewrite, hα.1]
    have htarget :
        ‖T x - T y‖ ^ 2 ≤
          ‖(x : H) - y‖ ^ 2 -
            α⁻¹ * (1 - α) * ‖((x : H) - y) - (T x - T y)‖ ^ 2 := by
      -- Rearranging isolates the `‖T x - T y‖^2` term.
      nlinarith [hgap]
    -- Rewrite the residual difference into the displayed `(Id - T)` form.
    simpa [div_eq_mul_inv, mul_comm, residual_difference_eq] using htarget
  · intro hS x y
    -- Start from clause (3) and rewrite it in the `d - t` form from the quadratic identity.
    have htarget :
        ‖T x - T y‖ ^ 2 ≤
          ‖(x : H) - y‖ ^ 2 -
            α⁻¹ * (1 - α) * ‖((x : H) - y) - (T x - T y)‖ ^ 2 := by
      simpa [div_eq_mul_inv, mul_comm, residual_difference_eq] using hS x y
    have hgap :
        0 ≤ ‖(x : H) - y‖ ^ 2 -
          α⁻¹ * (1 - α) * ‖((x : H) - y) - (T x - T y)‖ ^ 2 -
            ‖T x - T y‖ ^ 2 := by
      -- Move the right-hand side of clause (3) to the left.
      nlinarith [htarget]
    have hnonneg :
        0 ≤ α *
          (‖(x : H) - y‖ ^ 2 -
            α⁻¹ * (1 - α) * ‖((x : H) - y) - (T x - T y)‖ ^ 2 -
              ‖T x - T y‖ ^ 2) := by
      -- Multiply by the positive scalar `α`.
      nlinarith [hgap, hα.1]
    have hrewrite :
        0 ≤ α ^ 2 *
          (‖(x : H) - y‖ ^ 2 -
            ‖(1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y)‖ ^ 2) := by
      -- Lemma 2.17 identifies the same quadratic quantity.
      rw [alpha_sq_norm_sq_sub_inv_affine_combination_eq_norm_sub
        ((x : H) - y) (T x - T y) hα]
      exact hnonneg
    have hsq :
        ‖(1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y)‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2 := by
      -- Remove the positive factor `α^2`.
      have hgap' :
          0 ≤ ‖(x : H) - y‖ ^ 2 -
            ‖(1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y)‖ ^ 2 := by
        have hαsq : 0 < α ^ 2 := by
          nlinarith [hα.1]
        nlinarith [hrewrite, hαsq]
      nlinarith [hgap']
    -- Finally unsquare the estimate to recover the Lipschitz bound.
    have hsq' :
        ‖((1 - 1 / α) • (x : H) + (1 / α) • T x) -
            ((1 - 1 / α) • (y : H) + (1 / α) • T y)‖ ^ 2 ≤
          ‖(x : H) - y‖ ^ 2 := by
      rw [averaging_transform_sub]
      simpa using hsq
    exact (norm_sq_le_norm_sq_iff).1 hsq'

/-- Helper for Proposition 4.35: the affine transform is nonexpansive exactly when the inner
product inequality from clause (4) holds. -/
-- Proof sketch: reuse the squared nonexpansive estimate and rewrite the same quadratic gap with
-- the rearranged identity from Lemma 2.17.
private theorem averaging_transform_lipschitz_iff_inner_ineq
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {T : D → H} :
    LipschitzWith 1 (fun x : D ↦ (1 - 1 / α) • (x : H) + (1 / α) • T x) ↔
      ∀ x y : D,
        ‖T x - T y‖ ^ 2 + (1 - 2 * α) * ‖(x : H) - y‖ ^ 2 ≤
          2 * (1 - α) * inner ℝ ((x : H) - y) (T x - T y) := by
  rw [lipschitzWith_one_iff_pairwise_norm_sub_le]
  constructor
  · intro hS x y
    -- Square the pairwise nonexpansive estimate for the affine transform.
    have hSxy := hS x y
    rw [averaging_transform_sub] at hSxy
    have hsq :
        ‖(1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y)‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2 := by
      exact (norm_sq_le_norm_sq_iff).2 hSxy
    have hnonneg :
        0 ≤ α ^ 2 *
          (‖(x : H) - y‖ ^ 2 -
            ‖(1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y)‖ ^ 2) := by
      -- Multiplying by `α^2 > 0` preserves the squared comparison.
      nlinarith [hsq, hα.1]
    have hrewrite :
        0 ≤
          2 * (1 - α) * inner ℝ ((x : H) - y) (T x - T y) -
            (‖T x - T y‖ ^ 2 + (1 - 2 * α) * ‖(x : H) - y‖ ^ 2) := by
      -- Lemma 2.17 rewrites the scaled gap into the inner-product expression.
      rw [← alpha_sq_norm_sq_sub_inv_affine_combination_eq_rearranged
        ((x : H) - y) (T x - T y) hα]
      exact hnonneg
    -- Rearranging gives clause (4).
    nlinarith [hrewrite]
  · intro hS x y
    have hrewrite :
        0 ≤
          2 * (1 - α) * inner ℝ ((x : H) - y) (T x - T y) -
            (‖T x - T y‖ ^ 2 + (1 - 2 * α) * ‖(x : H) - y‖ ^ 2) := by
      -- Move clause (4) into the nonnegative form matching Lemma 2.17.
      nlinarith [hS x y]
    have hnonneg :
        0 ≤ α ^ 2 *
          (‖(x : H) - y‖ ^ 2 -
            ‖(1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y)‖ ^ 2) := by
      -- Rewrite the quadratic quantity back into the scaled norm gap.
      rw [alpha_sq_norm_sq_sub_inv_affine_combination_eq_rearranged
        ((x : H) - y) (T x - T y) hα]
      exact hrewrite
    have hsq :
        ‖(1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y)‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2 := by
      -- The positivity of `α^2` lets us remove the scalar factor.
      have hgap :
          0 ≤ ‖(x : H) - y‖ ^ 2 -
            ‖(1 - α⁻¹) • ((x : H) - y) + α⁻¹ • (T x - T y)‖ ^ 2 := by
        have hαsq : 0 < α ^ 2 := by
          nlinarith [hα.1]
        nlinarith [hnonneg, hαsq]
      nlinarith [hgap]
    -- Unsquare the estimate to recover nonexpansiveness.
    have hsq' :
        ‖((1 - 1 / α) • (x : H) + (1 / α) • T x) -
            ((1 - 1 / α) • (y : H) + (1 / α) • T y)‖ ^ 2 ≤
          ‖(x : H) - y‖ ^ 2 := by
      rw [averaging_transform_sub]
      simpa using hsq
    exact (norm_sq_le_norm_sq_iff).1 hsq'

/-- Proposition 4.35, clause `(1) ↔ (2)`: for `α ∈ (0, 1)`, a map is `α`-averaged exactly when
the standard affine transform `x ↦ (1 - 1 / α) x + (1 / α) T x` is nonexpansive. -/
private theorem averagedWith_iff_lipschitz_transform
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) {T : D → H} :
    AveragedWith α T ↔
      LipschitzWith 1 (fun x : D ↦ (1 - 1 / α) • (x : H) + (1 / α) • T x) := by
  let S : D → H := fun x : D ↦ (1 - 1 / α) • (x : H) + (1 / α) • T x
  have hα0 : α ≠ 0 := ne_of_gt hα.1
  constructor
  · intro hT
    rcases averagedWith_iff.mp hT with ⟨_, R, hR, hTR⟩
    have hSR : S = R := by
      ext x
      dsimp [S]
      rw [hTR]
      calc
        (1 - 1 / α) • (x : H) + (1 / α) • ((1 - α) • (x : H) + α • R x)
            = (1 - 1 / α) • (x : H) +
                (((1 / α) * (1 - α)) • (x : H) + ((1 / α) * α) • R x) := by
            rw [smul_add, smul_smul, smul_smul]
        _ = ((1 - 1 / α) + (1 / α) * (1 - α)) • (x : H) + ((1 / α) * α) • R x := by
            rw [← add_assoc, ← add_smul]
        _ = R x := by
            have hleft : (1 - 1 / α) + (1 / α) * (1 - α) = 0 := by
              field_simp [hα0]
              ring
            have hright : (1 / α) * α = 1 := by
              field_simp [hα0]
            rw [hleft, hright]
            simp
    change LipschitzWith 1 S
    rw [hSR]
    exact hR
  · intro hS
    have hTS : T = fun x : D ↦ (1 - α) • (x : H) + α • S x := by
      ext x
      symm
      calc
        (1 - α) • (x : H) + α • S x
            = (1 - α) • (x : H) + α • ((1 - 1 / α) • (x : H) + (1 / α) • T x) := by
                simp [S]
        _ = (1 - α) • (x : H) + ((α * (1 - 1 / α)) • (x : H) + (α * (1 / α)) • T x) := by
            rw [smul_add, smul_smul, smul_smul]
        _ = ((1 - α) + α * (1 - 1 / α)) • (x : H) + (α * (1 / α)) • T x := by
            rw [← add_assoc, ← add_smul]
        _ = T x := by
            have hleft : (1 - α) + α * (1 - 1 / α) = 0 := by
              field_simp [hα0]
              ring
            have hright : α * (1 / α) = 1 := by
              field_simp [hα0]
            rw [hleft, hright]
            simp
    exact averagedWith_iff.mpr ⟨hα, S, hS, hTS⟩

/-- Proposition 4.35, clause `(1) ↔ (3)`: for `α ∈ (0, 1)`, averagedness is equivalent to the
quadratic residual inequality. -/
theorem averagedWith_iff_residual_sqnorm_ineq
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) {T : D → H} :
    AveragedWith α T ↔
      ∀ x y : D,
        ‖T x - T y‖ ^ 2 ≤
          ‖(x : H) - y‖ ^ 2 -
            ((1 - α) / α) * ‖((x : H) - T x) - (y - T y)‖ ^ 2 := by
  rw [averagedWith_iff_lipschitz_transform hα, averaging_transform_lipschitz_iff_residual_ineq hα]

/-- Proposition 4.35, clause `(1) ↔ (4)`: for `α ∈ (0, 1)`, averagedness is equivalent to the
displayed inner-product inequality. -/
private theorem averagedWith_iff_inner_ineq
    {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1) {T : D → H} :
    AveragedWith α T ↔
      ∀ x y : D,
        ‖T x - T y‖ ^ 2 + (1 - 2 * α) * ‖(x : H) - y‖ ^ 2 ≤
          2 * (1 - α) * inner ℝ ((x : H) - y) (T x - T y) := by
  rw [averagedWith_iff_lipschitz_transform hα, averaging_transform_lipschitz_iff_inner_ineq hα]

/-- Proposition 4.35: for `α ∈ (0,1)`, the four standard characterizations of an
`α`-averaged operator on a subset of a real Hilbert space are equivalent. -/
-- Proof sketch: prove `(1) ↔ (2)` by solving the affine identity for the companion map,
-- prove `(2) ↔ (3)` by expanding the norm of
-- `((1 - 1 / α) • (x - y) + (1 / α) • (T x - T y))`, and obtain `(3) ↔ (4)` by expanding
-- `‖((x - T x) - (y - T y))‖ ^ 2`.
theorem averagedWith_tfae (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (T : D → H) :
    [ AveragedWith α T,
      LipschitzWith 1 (fun x : D ↦ (1 - 1 / α) • (x : H) + (1 / α) • T x),
      ∀ x y : D,
        ‖T x - T y‖ ^ 2 ≤
          ‖(x : H) - y‖ ^ 2 -
            ((1 - α) / α) * ‖((x : H) - T x) - (y - T y)‖ ^ 2,
      ∀ x y : D,
        ‖T x - T y‖ ^ 2 + (1 - 2 * α) * ‖(x : H) - y‖ ^ 2 ≤
          2 * (1 - α) * inner ℝ ((x : H) - y) (T x - T y) ].TFAE := by
  tfae_have 1 ↔ 2 := by
    exact averagedWith_iff_lipschitz_transform hα
  tfae_have 2 ↔ 3 := by
    exact averaging_transform_lipschitz_iff_residual_ineq hα
  tfae_have 2 ↔ 4 := by
    exact averaging_transform_lipschitz_iff_inner_ineq hα
  tfae_finish

end

/-! Source item: Chap04/Remark_4_36 -/

section


variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {D : Set H} {T : H → H} {α : ℝ}

private lemma companion_fixed_of_isFixedPt
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {T R : D → H} (hT : ∀ x : D, T x = (1 - α) • (x : H) + α • R x)
    {p : D} (hp : T p = p) :
    R p = p := by
  have h_avg : (p : H) = (1 - α) • (p : H) + α • R p := by
    calc
      (p : H) = T p := hp.symm
      _ = (1 - α) • (p : H) + α • R p := hT p
  have hsmul : α • (p : H) = α • R p := by
    have hp_sub : (p : H) - (1 - α) • (p : H) = α • (p : H) := by
      module
    have hsub : (p : H) - (1 - α) • (p : H) = α • R p := by
      simpa using congrArg (fun z ↦ z - (1 - α) • (p : H)) h_avg
    calc
      α • (p : H) = (p : H) - (1 - α) • (p : H) := hp_sub.symm
      _ = α • R p := hsub
  have hα_ne : α ≠ 0 := ne_of_gt hα.1
  exact smul_right_injective H hα_ne hsmul.symm

private lemma averaged_sqnorm_le_sqnorm_sub_correction
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {T R : D → H} (hR : LipschitzWith 1 R)
    (hT : ∀ x : D, T x = (1 - α) • (x : H) + α • R x)
    (x p : D) (hp : T p = p) :
    ‖T x - p‖ ^ 2 + α * (1 - α) * ‖(x : H) - R x‖ ^ 2 ≤ ‖(x : H) - p‖ ^ 2 := by
  have hRp : R p = p := companion_fixed_of_isFixedPt hα hT hp
  have hR_le : ‖R x - p‖ ≤ ‖(x : H) - p‖ := by
    simpa [Subtype.dist_eq, dist_eq_norm, hRp, one_mul] using hR.dist_le_mul x p
  have hR_sq_le : ‖R x - p‖ ^ 2 ≤ ‖(x : H) - p‖ ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hR_le 2
  have hTx_vec :
      T x - p = α • (R x - p) + (1 - α) • ((x : H) - p) := by
    rw [hT x]
    module
  have hTx_rewrite :
      ‖T x - p‖ ^ 2 = ‖α • (R x - p) + (1 - α) • ((x : H) - p)‖ ^ 2 := by
    simp [hTx_vec]
  have hdiff_rewrite :
      ‖(x : H) - R x‖ ^ 2 = ‖(R x - p) - ((x : H) - p)‖ ^ 2 := by
    congr 1
    rw [show (R x - p) - ((x : H) - p) = R x - x by abel]
    rw [norm_sub_rev]
  have h_affine :
      ‖T x - p‖ ^ 2 + α * (1 - α) * ‖(x : H) - R x‖ ^ 2 =
        α * ‖R x - p‖ ^ 2 + (1 - α) * ‖(x : H) - p‖ ^ 2 := by
    rw [hTx_rewrite, hdiff_rewrite]
    simpa using
      norm_sq_affine_combination_add_weighted_norm_sub_sq (R x - p) ((x : H) - p) α
  calc
    ‖T x - p‖ ^ 2 + α * (1 - α) * ‖(x : H) - R x‖ ^ 2
        = α * ‖R x - p‖ ^ 2 + (1 - α) * ‖(x : H) - p‖ ^ 2 := h_affine
    _ ≤ α * ‖(x : H) - p‖ ^ 2 + (1 - α) * ‖(x : H) - p‖ ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hR_sq_le hα.1.le) le_rfl
    _ = ‖(x : H) - p‖ ^ 2 := by ring

private lemma companion_ne_of_not_isFixedPt
    {T R : D → H} (hT : ∀ x : D, T x = (1 - α) • (x : H) + α • R x)
    {x : D} (hx : T x ≠ x) :
    (x : H) ≠ R x := by
  intro hRx
  have hTx : T x = x := by
    calc
      T x = (1 - α) • (x : H) + α • R x := hT x
      _ = (1 - α) • (x : H) + α • (x : H) := by rw [← hRx]
      _ = ((1 - α) + α) • (x : H) := by rw [← add_smul]
      _ = (1 : ℝ) • (x : H) := by congr 1; ring
      _ = x := one_smul ℝ (x : H)
  exact hx hTx

-- Proof sketch: unpack the canonical `AveragedWith` witness on the restriction to `D`, show that
-- fixed points of the averaged map are fixed by its nonexpansive companion, and then apply the
-- Hilbert-space affine norm identity with the resulting positive correction term.
/-- Remark 4.36: an averaged self-map on `D` is strictly quasinonexpansive on `D`. -/
theorem averaged_strictlyQuasinonexpansiveOn
    (hT : AveragedWith α (fun x : D ↦ T x)) :
    StrictlyQuasinonexpansiveOn D T := by
  rcases averagedWith_iff.mp hT with ⟨hα, R, hR, hTR⟩
  have hrepr : ∀ x : D, T x = (1 - α) • (x : H) + α • R x := by
    intro x
    simpa using congrArg (fun f : D → H ↦ f x) hTR
  rw [strictlyQuasinonexpansiveOn_iff]
  intro x hx p hp
  rcases mem_fixedPointSetOn_iff.mp hp with ⟨hpD, hpfix⟩
  let x' : D := ⟨x, hx.1⟩
  let p' : D := ⟨p, hpD⟩
  have hpfix' : T p' = p' := by
    simpa [p'] using hpfix
  have hsq :
      ‖T x - p‖ ^ 2 + α * (1 - α) * ‖x - R x'‖ ^ 2 ≤ ‖x - p‖ ^ 2 := by
    simpa [x', p'] using averaged_sqnorm_le_sqnorm_sub_correction hα hR hrepr x' p' hpfix'
  have hxfix_ne : T x' ≠ x' := by
    intro hxfix
    exact hx.2 <| mem_fixedPointSetOn_iff.mpr ⟨hx.1, by simpa [x'] using hxfix⟩
  have hxR_ne : x ≠ R x' := by
    simpa [x'] using companion_ne_of_not_isFixedPt hrepr hxfix_ne
  have hnorm_pos : 0 < ‖x - R x'‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hxR_ne
  have hcorr_pos : 0 < α * (1 - α) * ‖x - R x'‖ ^ 2 := by
    have h_one_sub_pos : 0 < 1 - α := sub_pos.mpr hα.2
    have hnorm_sq_pos : 0 < ‖x - R x'‖ ^ 2 := by nlinarith
    exact mul_pos (mul_pos hα.1 h_one_sub_pos) hnorm_sq_pos
  have hTx_sq_lt : ‖T x - p‖ ^ 2 < ‖x - p‖ ^ 2 := by
    nlinarith [hsq, hcorr_pos]
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hTx_sq_lt

/-- An averaged self-map on `D` is quasinonexpansive on `D`. -/
theorem averaged_quasinonexpansiveOn
    (hT : AveragedWith α (fun x : D ↦ T x)) :
    QuasinonexpansiveOn D T :=
  (averaged_strictlyQuasinonexpansiveOn hT).quasinonexpansiveOn

end

/-! Source item: Chap04/Remark_4_37 -/

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {D : Set H} {α : ℝ} {T : D → H}

/-- Remark 4.37: if `T : D → H` is `α`-averaged for some `α ∈ (0, 1 / 2]`, then `T` is firmly
nonexpansive on `D`. -/
theorem firmlyNonexpansiveOn_of_averagedWith_le_half
    (hT : AveragedWith α T) (hα : α ≤ 1 / 2) :
    FirmlyNonexpansiveOn D T := by
  rw [firmlyNonexpansiveOn_iff]
  have hαIoo : α ∈ Set.Ioo (0 : ℝ) 1 := hT.mem_Ioo
  have hresidual :=
    (averagedWith_iff_residual_sqnorm_ineq hαIoo).mp hT
  intro x y
  have hcoeff : 1 ≤ (1 - α) / α := by
    have haux : 0 ≤ (1 - 2 * α) / α := by
      exact div_nonneg (by nlinarith [hα]) hαIoo.1.le
    have hsplit : (1 - α) / α = 1 + (1 - 2 * α) / α := by
      field_simp [hαIoo.1.ne']
      ring
    nlinarith [haux, hsplit]
  have hineq :
      ‖T x - T y‖ ^ (2 : ℕ) ≤
        ‖(x : H) - y‖ ^ (2 : ℕ) -
          ‖((x : H) - T x - (y - T y))‖ ^ (2 : ℕ) := by
    have hxy := hresidual x y
    nlinarith [sq_nonneg ‖((x : H) - T x) - (y - T y)‖, hcoeff]
  have hnorm :
      ‖((x : H) - y) - (T x - T y)‖ ^ (2 : ℕ) =
        ‖(x : H) - y‖ ^ (2 : ℕ) - 2 * inner ℝ ((x : H) - y) (T x - T y) +
          ‖T x - T y‖ ^ (2 : ℕ) := by
    simpa using norm_sub_sq_real ((x : H) - y) (T x - T y)
  have hrewrite :
      ((x : H) - T x) - (y - T y) = ((x : H) - y) - (T x - T y) := by
    abel
  rw [hrewrite] at hineq
  nlinarith [hineq, hnorm]

end

/-! Source item: Chap04/Proposition_4_38 -/

section

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {D : Set H}

/-- The explicit affine companion used in Proposition 4.38. -/
private noncomputable def lipschitz_lt_one_companion (ρ : ℝ) (T : D → H) : D → H :=
  fun x ↦ ((ρ - 1) / (ρ + 1)) • (x : H) + (2 / (ρ + 1)) • T x

private lemma companion_coefficient_simplifications {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) :
    |(ρ - 1) / (ρ + 1)| = (1 - ρ) / (ρ + 1) ∧
      |(2 : ℝ) / (ρ + 1)| = 2 / (ρ + 1) ∧
        ((1 - ρ) / (ρ + 1) + (2 * ρ) / (ρ + 1) = 1) := by
  have hden : 0 < ρ + 1 := by
    linarith [hρ.1]
  have hnum_nonpos : ρ - 1 ≤ 0 := by
    linarith [hρ.2]
  have hfrac_nonpos : (ρ - 1) / (ρ + 1) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos hden.le
  have htwo_nonneg : 0 ≤ (2 : ℝ) / (ρ + 1) := by
    exact div_nonneg (by norm_num) hden.le
  refine ⟨?_, ?_, ?_⟩
  · calc
      |(ρ - 1) / (ρ + 1)| = -((ρ - 1) / (ρ + 1)) := abs_of_nonpos hfrac_nonpos
      _ = (1 - ρ) / (ρ + 1) := by
        field_simp [hden.ne']
        ring
  · exact abs_of_nonneg htwo_nonneg
  · field_simp [hden.ne']
    ring

private lemma companion_difference_eq {ρ : ℝ} {T : D → H} (x y : D) :
    lipschitz_lt_one_companion ρ T x - lipschitz_lt_one_companion ρ T y =
      ((ρ - 1) / (ρ + 1)) • ((x : H) - y) + (2 / (ρ + 1)) • (T x - T y) := by
  simp [lipschitz_lt_one_companion, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

private lemma companion_pairwise_nonexpansive {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) {T : D → H}
    (hT : LipschitzWith (Real.toNNReal ρ) T) :
    ∀ x y : D,
      ‖lipschitz_lt_one_companion ρ T x - lipschitz_lt_one_companion ρ T y‖ ≤ ‖(x : H) - y‖ := by
  intro x y
  rcases companion_coefficient_simplifications hρ with ⟨habs₁, habs₂, hsum⟩
  have hden : 0 < ρ + 1 := by
    linarith [hρ.1]
  have htwo_nonneg : 0 ≤ (2 : ℝ) / (ρ + 1) := by
    exact div_nonneg (by norm_num) hden.le
  have hTxy : ‖T x - T y‖ ≤ ρ * ‖(x : H) - y‖ := by
    simpa [Subtype.dist_eq, dist_eq_norm, Real.toNNReal_of_nonneg hρ.1.le] using hT.dist_le_mul x y
  rw [companion_difference_eq]
  calc
    ‖((ρ - 1) / (ρ + 1)) • ((x : H) - y) + (2 / (ρ + 1)) • (T x - T y)‖
      ≤ ‖((ρ - 1) / (ρ + 1)) • ((x : H) - y)‖ + ‖(2 / (ρ + 1)) • (T x - T y)‖ :=
        norm_add_le _ _
    _ = ‖(ρ - 1) / (ρ + 1)‖ * ‖(x : H) - y‖ + ‖(2 : ℝ) / (ρ + 1)‖ * ‖T x - T y‖ := by
      rw [norm_smul, norm_smul]
    _ = |(ρ - 1) / (ρ + 1)| * ‖(x : H) - y‖ + |(2 : ℝ) / (ρ + 1)| * ‖T x - T y‖ := by
      rw [abs_div, abs_div]
      simp [Real.norm_eq_abs]
    _ = ((1 - ρ) / (ρ + 1)) * ‖(x : H) - y‖ + (2 / (ρ + 1)) * ‖T x - T y‖ := by
      rw [habs₁, habs₂]
    _ ≤ ((1 - ρ) / (ρ + 1)) * ‖(x : H) - y‖ + (2 / (ρ + 1)) * (ρ * ‖(x : H) - y‖) := by
      have hscaled :
          (2 / (ρ + 1)) * ‖T x - T y‖ ≤ (2 / (ρ + 1)) * (ρ * ‖(x : H) - y‖) := by
        exact mul_le_mul_of_nonneg_left hTxy htwo_nonneg
      nlinarith [hscaled]
    _ = (((1 - ρ) / (ρ + 1)) + (2 * ρ) / (ρ + 1)) * ‖(x : H) - y‖ := by
      ring
    _ = ‖(x : H) - y‖ := by
      rw [hsum, one_mul]

private theorem companion_lipschitzWith_one {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) {T : D → H}
    (hT : LipschitzWith (Real.toNNReal ρ) T) :
    LipschitzWith 1 (lipschitz_lt_one_companion ρ T) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  simpa [Subtype.dist_eq, dist_eq_norm] using companion_pairwise_nonexpansive hρ hT x y

private lemma companion_affine_reconstruction {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) {T : D → H} :
    T = fun x : D ↦
      (1 - ((ρ + 1) / 2 : ℝ)) • (x : H) +
        (((ρ + 1) / 2 : ℝ)) • lipschitz_lt_one_companion ρ T x := by
  ext x
  have hden : ρ + 1 ≠ 0 := by
    linarith [hρ.1]
  have hx :
      1 - ((ρ + 1) / 2 : ℝ) + ((ρ + 1) / 2 : ℝ) * ((ρ - 1) / (ρ + 1)) = 0 := by
    field_simp [hden]
    ring
  have hTx : ((ρ + 1) / 2 : ℝ) * (2 / (ρ + 1)) = 1 := by
    field_simp [hden]
  have hexpand :
      (1 - ((ρ + 1) / 2 : ℝ)) • (x : H) +
          (((ρ + 1) / 2 : ℝ)) • lipschitz_lt_one_companion ρ T x =
        (1 - ((ρ + 1) / 2 : ℝ) + ((ρ + 1) / 2 : ℝ) * ((ρ - 1) / (ρ + 1))) • (x : H) +
          (((ρ + 1) / 2 : ℝ) * (2 / (ρ + 1))) • T x := by
    simp [lipschitz_lt_one_companion, smul_add, mul_smul, add_smul, add_assoc, add_left_comm,
      add_comm]
  calc
    T x = 0 • (x : H) + 1 • T x := by
      simp
    _ = (1 - ((ρ + 1) / 2 : ℝ) + ((ρ + 1) / 2 : ℝ) * ((ρ - 1) / (ρ + 1))) • (x : H) +
          (((ρ + 1) / 2 : ℝ) * (2 / (ρ + 1))) • T x := by
      simp [hx, hTx]
    _ = (1 - ((ρ + 1) / 2 : ℝ)) • (x : H) +
          (((ρ + 1) / 2 : ℝ)) • lipschitz_lt_one_companion ρ T x := by
      rw [hexpand]

private lemma averaged_parameter_mem_Ioo {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) :
    (ρ + 1) / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor <;> nlinarith [hρ.1, hρ.2]

-- Proof sketch: define the affine companion
-- `R x = ((ρ - 1) / (ρ + 1)) • x + (2 / (ρ + 1)) • T x`, show it is nonexpansive by the
-- `ρ`-Lipschitz estimate, and then rewrite `T` as
-- `(1 - (ρ + 1) / 2) Id + ((ρ + 1) / 2) R`.
/-- Proposition 4.38: if `T : D → H` is `ρ`-Lipschitz with `0 < ρ < 1`, then `T` is
`((ρ + 1) / 2)`-averaged. -/
theorem averagedWith_of_lipschitz_lt_one {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) {T : D → H}
    (hT : LipschitzWith (Real.toNNReal ρ) T) :
    AveragedWith ((ρ + 1) / 2 : ℝ) T := by
  refine averagedWith_iff.mpr ?_
  refine ⟨averaged_parameter_mem_Ioo hρ, lipschitz_lt_one_companion ρ T, ?_, ?_⟩
  · exact companion_lipschitzWith_one hρ hT
  · exact companion_affine_reconstruction hρ

end

/-! Source item: Chap04/Proposition_4_39 -/

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 4.39: scaling `T` by the positive scalar `β` turns cocoercivity into
firm nonexpansiveness. -/
-- Proof sketch: multiply the cocoercive inequality by `β > 0` and simplify the scaled norm and
-- inner-product terms.
private lemma cocoerciveOn_iff_firmlyNonexpansiveOn_smul_prop39 {D : Set H} {β : ℝ} (hβ : 0 < β)
    (T : D → H) :
    CocoerciveOn β D T ↔ FirmlyNonexpansiveOn D (fun x : D ↦ β • T x) := by
  rw [CocoerciveOn, firmlyNonexpansiveOn_iff]
  constructor
  · intro hT x y
    -- Multiply the cocoercive inequality by `β` so it matches the scaled firm inequality.
    have hscaled :
        β * (β * ‖T x - T y‖ ^ 2) ≤ β * inner ℝ ((x : H) - y) (T x - T y) := by
      exact mul_le_mul_of_nonneg_left (hT.2 x y) hβ.le
    have hnorm :
        ‖β • T x - β • T y‖ ^ 2 = β * (β * ‖T x - T y‖ ^ 2) := by
      calc
        ‖β • T x - β • T y‖ ^ 2 = ‖β • (T x - T y)‖ ^ 2 := by rw [smul_sub]
        _ = (β * ‖T x - T y‖) ^ 2 := by simp [norm_smul, abs_of_nonneg hβ.le]
        _ = β * (β * ‖T x - T y‖ ^ 2) := by
          rw [pow_two]
          ring
    have hinner :
        inner ℝ ((x : H) - y) (β • T x - β • T y) =
          β * inner ℝ ((x : H) - y) (T x - T y) := by
      rw [← smul_sub, real_inner_smul_right]
    rw [hnorm, hinner]
    exact hscaled
  · intro hT
    refine ⟨hβ, ?_⟩
    intro x y
    -- Simplifying the firm inequality for the scaled map leaves the cocoercive inequality.
    have hscaled := hT x y
    have hnorm :
        ‖β • T x - β • T y‖ ^ 2 = β * (β * ‖T x - T y‖ ^ 2) := by
      calc
        ‖β • T x - β • T y‖ ^ 2 = ‖β • (T x - T y)‖ ^ 2 := by rw [smul_sub]
        _ = (β * ‖T x - T y‖) ^ 2 := by simp [norm_smul, abs_of_nonneg hβ.le]
        _ = β * (β * ‖T x - T y‖ ^ 2) := by
          rw [pow_two]
          ring
    have hinner :
        inner ℝ ((x : H) - y) (β • T x - β • T y) =
          β * inner ℝ ((x : H) - y) (T x - T y) := by
      rw [← smul_sub, real_inner_smul_right]
    rw [hnorm, hinner] at hscaled
    nlinarith

/-- Helper for Proposition 4.39: the reflector of the residual map of `β • T` is exactly the
affine transform from Proposition 4.35 applied to `x ↦ x - γ • T x`, with averaging parameter
`α = γ / (2β)`. -/
-- Proof sketch: both maps simplify to `x ↦ x - 2β • T x` after clearing the scalar coefficients.
private lemma reflected_residual_smul_eq_averaging_transform {D : Set H} {β γ α : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hα : α = γ / (2 * β)) (T : D → H) :
    reflectedMap D (residualMap D (fun x : D ↦ β • T x)) =
      fun x : D ↦ (1 - 1 / α) • (x : H) + (1 / α) • ((x : H) - γ • T x) := by
  ext x
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  -- First normalize the reflector of the residual map to the textbook expression `Id - 2βT`.
  calc
    reflectedMap D (residualMap D (fun x : D ↦ β • T x)) x
        = (x : H) - (2 * β) • T x := by
          simp [reflectedMap, residualMap, two_smul, smul_smul, sub_eq_add_neg,
            add_assoc, add_left_comm, add_comm]
    _ = (1 - 1 / α) • (x : H) + (1 / α) • ((x : H) - γ • T x) := by
      rw [hα]
      have hsum : (1 - 1 / (γ / (2 * β))) + 1 / (γ / (2 * β)) = (1 : ℝ) := by
        field_simp [hβ0, hγ0]
        ring
      have hcoeff : (1 / (γ / (2 * β))) * γ = 2 * β := by
        field_simp [hβ0, hγ0]
      calc
        (x : H) - (2 * β) • T x
            = (1 : ℝ) • (x : H) - (2 * β) • T x := by simp
        _ =
            ((1 - 1 / (γ / (2 * β))) + 1 / (γ / (2 * β))) • (x : H) -
              ((1 / (γ / (2 * β))) * γ) • T x := by
            rw [hsum, hcoeff]
        _ =
            (1 - 1 / (γ / (2 * β))) • (x : H) +
              (1 / (γ / (2 * β))) • ((x : H) - γ • T x) := by
            simp [sub_eq_add_neg, smul_smul, add_assoc, add_left_comm, add_comm,
              add_smul]

-- Proof sketch: combine the `β`-cocoercive iff `1 / 2`-averaged characterization for
-- `x ↦ β • T x` with the affine characterization of averaged maps. Rewriting the averaging
-- parameter from `1 / 2` to `γ / (2 * β)` identifies the companion map with `fun x ↦ x - γ • T x`.
/-- Proposition 4.39: on a subset `D` of a real inner product space, a map `T : D → H` is
`β`-cocoercive if and only if the map `x ↦ x - γ • T x` is `γ / (2 * β)`-averaged whenever
`0 < β` and `γ ∈ ]0, 2β[`. -/
theorem cocoerciveOn_iff_averagedWith_id_sub_smul
    {D : Set H} {β γ : ℝ} (hβ : 0 < β)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) (2 * β)) (T : D → H) :
    CocoerciveOn β D T ↔
      AveragedWith (γ / (2 * β)) (fun x : D ↦ (x : H) - γ • T x) := by
  let α : ℝ := γ / (2 * β)
  let S : D → H := fun x : D ↦ β • T x
  let R : D → H := residualMap D S
  let U : D → H := fun x : D ↦ (x : H) - γ • T x
  have htwoβ : 0 < 2 * β := by
    nlinarith
  have hαmem : α ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · -- The averaging parameter is positive because both `γ` and `2β` are positive.
      dsimp [α]
      exact div_pos hγ.1 htwoβ
    · -- The upper bound `γ < 2β` is exactly the condition `γ / (2β) < 1`.
      dsimp [α]
      exact (div_lt_one htwoβ).2 hγ.2
  have htransform :
      reflectedMap D R =
        fun x : D ↦ (1 - 1 / α) • (x : H) + (1 / α) • U x := by
    -- This is the affine bridge between Proposition 4.4 and Proposition 4.35.
    have htransform' :
        reflectedMap D R =
          fun x : D ↦
            (1 - 1 / (γ / (2 * β))) • (x : H) + (1 / (γ / (2 * β))) • U x := by
      simpa [S, R, U] using
        reflected_residual_smul_eq_averaging_transform hβ hγ.1 rfl T
    simpa [α] using
      htransform'
  constructor
  · intro hT
    -- The source proof first rescales `T` to a firmly nonexpansive map.
    have hFirmS : FirmlyNonexpansiveOn D S := by
      simpa [S] using
        (cocoerciveOn_iff_firmlyNonexpansiveOn_smul_prop39 hβ T).mp hT
    -- Proposition 4.4 passes firm nonexpansiveness to the residual map.
    have hFirmR : FirmlyNonexpansiveOn D R := by
      exact (firmlyNonexpansiveOn_residualMap_iff D S).2 hFirmS
    -- Applying Proposition 4.4 again turns the residual into a nonexpansive reflector.
    have hReflect :
        ∀ x y : D, ‖reflectedMap D R x - reflectedMap D R y‖ ≤ ‖(x : H) - y‖ := by
      exact (reflectedMap_nonexpansive_iff_firmlyNonexpansiveOn D R).2 hFirmR
    have hAffinePairwise :
        ∀ x y : D,
          ‖((1 - 1 / α) • (x : H) + (1 / α) • U x) -
              ((1 - 1 / α) • (y : H) + (1 / α) • U y)‖ ≤ ‖(x : H) - y‖ := by
      -- Rewrite the reflector into the affine transform from Proposition 4.35.
      simpa [htransform] using hReflect
    have hAffineLip :
        LipschitzWith 1 (fun x : D ↦ (1 - 1 / α) • (x : H) + (1 / α) • U x) := by
      -- Pairwise nonexpansiveness is the same as `LipschitzWith 1` on the subtype domain.
      refine LipschitzWith.of_dist_le_mul ?_
      intro x y
      simpa [Subtype.dist_eq, dist_eq_norm] using hAffinePairwise x y
    have hAvgWith : AveragedWith α U := by
      -- Proposition 4.35 recognizes this affine transform as the averagedness criterion.
      exact (List.TFAE.out (averagedWith_tfae α hαmem U) 1 0).mp hAffineLip
    exact hAvgWith
  · intro hT
    have hAffineLip :
        LipschitzWith 1 (fun x : D ↦ (1 - 1 / α) • (x : H) + (1 / α) • U x) := by
      -- Proposition 4.35 turns averagedness back into nonexpansiveness of the affine transform.
      exact (List.TFAE.out (averagedWith_tfae α hαmem U) 0 1).mp hT
    have hAffinePairwise :
        ∀ x y : D,
          ‖((1 - 1 / α) • (x : H) + (1 / α) • U x) -
              ((1 - 1 / α) • (y : H) + (1 / α) • U y)‖ ≤ ‖(x : H) - y‖ := by
      intro x y
      simpa [Subtype.dist_eq, dist_eq_norm] using hAffineLip.dist_le_mul x y
    have hReflect :
        ∀ x y : D, ‖reflectedMap D R x - reflectedMap D R y‖ ≤ ‖(x : H) - y‖ := by
      -- Rewrite the affine transform back into the reflector of the residual map.
      simpa [htransform] using hAffinePairwise
    have hFirmR : FirmlyNonexpansiveOn D R := by
      -- Proposition 4.4 recovers firm nonexpansiveness of the residual map.
      exact (reflectedMap_nonexpansive_iff_firmlyNonexpansiveOn D R).1 hReflect
    have hFirmS : FirmlyNonexpansiveOn D S := by
      -- Applying Proposition 4.4 once more returns to the scaled operator `β • T`.
      exact (firmlyNonexpansiveOn_residualMap_iff D S).1 hFirmR
    -- Undo the scaling bridge to recover cocoercivity of `T`.
    simpa [S] using
      (cocoerciveOn_iff_firmlyNonexpansiveOn_smul_prop39 hβ T).mpr hFirmS

end

/-! Source item: Chap04/Proposition_4_40 -/

section

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {D : Set H} {α lam : ℝ} {T : D → H}

/-- Helper for Proposition 4.40: substituting the affine companion of an averaged map into the
relaxed map formula yields the expected new affine companion. -/
private lemma relaxedMap_eq_affine {R : D → H}
    (hT : T = fun x : D ↦ (1 - α) • (x : H) + α • R x) :
    (fun x : D ↦ (1 - lam) • (x : H) + lam • T x) =
      fun x : D ↦ (1 - lam * α) • (x : H) + (lam * α) • R x := by
  ext x
  calc
    (1 - lam) • (x : H) + lam • T x
        = (1 - lam) • (x : H) + lam • ((1 - α) • (x : H) + α • R x) := by
            simp [hT]
    _ = (1 - lam) • (x : H) + (lam * (1 - α)) • (x : H) + (lam * α) • R x := by
          rw [smul_add, ← mul_smul, ← mul_smul]
          simp [add_assoc]
    _ = ((1 - lam) + lam * (1 - α)) • (x : H) + (lam * α) • R x := by
          rw [← add_smul]
    _ = (1 - lam * α) • (x : H) + (lam * α) • R x := by
          congr 1
          ring_nf

/-- Helper for Proposition 4.40: if the relaxed map has affine companion with coefficient
`lam * α`, then solving the identity for `T` recovers the original affine companion when
`lam ≠ 0`. -/
private lemma affine_of_relaxedMap_eq {R : D → H} (hlam0 : lam ≠ 0)
    (hS : (fun x : D ↦ (1 - lam) • (x : H) + lam • T x) =
      fun x : D ↦ (1 - lam * α) • (x : H) + (lam * α) • R x) :
    T = fun x : D ↦ (1 - α) • (x : H) + α • R x := by
  ext x
  have hx := congrArg (fun f ↦ f x) hS
  have hx' : (1 - lam) • (x : H) + lam • T x =
      (1 - lam) • (x : H) + lam • ((1 - α) • (x : H) + α • R x) := by
    calc
      (1 - lam) • (x : H) + lam • T x
          = (1 - lam * α) • (x : H) + (lam * α) • R x := hx
      _ = ((1 - lam) + lam * (1 - α)) • (x : H) + (lam * α) • R x := by
            congr 1
            ring_nf
      _ = (1 - lam) • (x : H) + (lam * (1 - α)) • (x : H) + (lam * α) • R x := by
            rw [add_smul]
      _ = (1 - lam) • (x : H) + lam • ((1 - α) • (x : H) + α • R x) := by
            rw [smul_add, ← mul_smul, ← mul_smul]
            simp [add_assoc]
  have hx'' : lam • T x = lam • ((1 - α) • (x : H) + α • R x) := by
    exact add_left_cancel hx'
  have hx''' := congrArg (fun y : H ↦ lam⁻¹ • y) hx''
  simpa [smul_smul, hlam0] using hx'''

-- Proof sketch: expand `AveragedWith α T` using the canonical affine-companion description,
-- substitute this identity into the relaxation `x ↦ (1 - λ) • x + λ • T x`, and simplify to
-- `(1 - λ * α) • Id + (λ * α) • R`; for the converse, solve the same affine identity for `T`.
/-- Proposition 4.40: if `α ∈ (0,1)` and `λ ∈ (0, 1 / α)`, then `T` is `α`-averaged if and only
if the relaxation `x ↦ (1 - λ) • x + λ • T x` is `(λ * α)`-averaged. -/
theorem averagedWith_iff_averagedWith_relaxedMap
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hlam : lam ∈ Set.Ioo (0 : ℝ) (1 / α)) :
    AveragedWith α T ↔
      AveragedWith (lam * α) (fun x : D ↦ (1 - lam) • (x : H) + lam • T x) := by
  have hlam_mul : lam * α ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨mul_pos hlam.1 hα.1, ?_⟩
    have hlt : lam * α < (1 / α) * α := by
      exact mul_lt_mul_of_pos_right hlam.2 hα.1
    have hα0 : α ≠ 0 := ne_of_gt hα.1
    simpa [div_eq_mul_inv, hα0] using hlt
  rw [averagedWith_iff, averagedWith_iff]
  constructor
  · rintro ⟨_, R, hR, hT⟩
    exact ⟨hlam_mul, R, hR, relaxedMap_eq_affine hT⟩
  · rintro ⟨_, R, hR, hS⟩
    exact ⟨hα, R, hR, affine_of_relaxedMap_eq (ne_of_gt hlam.1) hS⟩

end

/-! Source item: Chap04/Corollary_4_41 -/

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Corollary 4.41: on a subset `D` of a real Hilbert space, `T` is firmly nonexpansive if and
only if its relaxation `x ↦ (1 - λ) • x + λ • T x` is `(λ / 2)`-averaged for `λ ∈ (0, 2)`. -/
theorem firmlyNonexpansiveOn_iff_relaxation_averagedWith {D : Set H} (T : D → H)
    {lam : ℝ} (hlam : lam ∈ Set.Ioo (0 : ℝ) 2) :
    FirmlyNonexpansiveOn D T ↔
      AveragedWith (lam / 2) (fun x : D ↦ (1 - lam) • (x : H) + lam • T x) := by
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    norm_num
  have hlam' : lam ∈ Set.Ioo (0 : ℝ) (1 / (1 / 2 : ℝ)) := by
    simpa using hlam
  calc
    FirmlyNonexpansiveOn D T ↔ AveragedWith (1 / 2 : ℝ) T := by
      exact firmlyNonexpansiveOn_iff_averagedWith_half T
    _ ↔ AveragedWith (lam * (1 / 2 : ℝ)) (fun x : D ↦ (1 - lam) • (x : H) + lam • T x) := by
      exact averagedWith_iff_averagedWith_relaxedMap hhalf hlam'
    _ ↔ AveragedWith (lam / 2) (fun x : D ↦ (1 - lam) • (x : H) + lam • T x) := by
      simp [div_eq_mul_inv]

end

/-! Source item: Chap04/Proposition_4_42 -/

universe v

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {D : Set H} {I : Type v} [Fintype I]

private lemma weighted_averagingParameter_mem_Ioo (ω α : I → ℝ)
    (hω : ∀ i, ω i ∈ Set.Icc (0 : ℝ) 1) (hω_sum : ∑ i, ω i = 1)
    (hα : ∀ i, α i ∈ Set.Ioo (0 : ℝ) 1) :
    (∑ i, ω i * α i) ∈ Set.Ioo (0 : ℝ) 1 := by
  classical
  let αbar : ℝ := ∑ i, ω i * α i
  have hω_exists : ∃ i, ω i ≠ 0 := by
    by_contra hω_exists
    have hω_zero : ∀ i, ω i = 0 := by
      intro i
      by_contra hωi
      exact hω_exists ⟨i, hωi⟩
    simp [hω_zero] at hω_sum
  rcases hω_exists with ⟨i₀, hωi₀_ne⟩
  have hωi₀_pos : 0 < ω i₀ := by
    exact lt_of_le_of_ne (hω i₀).1 (Ne.symm hωi₀_ne)
  have hαbar_pos : 0 < αbar := by
    have hi₀_pos : 0 < ω i₀ * α i₀ := mul_pos hωi₀_pos (hα i₀).1
    have hi₀_le : ω i₀ * α i₀ ≤ αbar := by
      simpa [αbar] using
        (Finset.single_le_sum
          (fun j _ ↦ mul_nonneg (hω j).1 (hα j).1.le)
          (by simp : i₀ ∈ (Finset.univ : Finset I)))
    exact lt_of_lt_of_le hi₀_pos hi₀_le
  have hαbar_lt : αbar < 1 := by
    let δ : ℝ := ∑ i, ω i * (1 - α i)
    have hδ_pos : 0 < δ := by
      have hi₀_pos : 0 < ω i₀ * (1 - α i₀) := by
        have hαi₀_lt : 0 < 1 - α i₀ := sub_pos.mpr (hα i₀).2
        exact mul_pos hωi₀_pos hαi₀_lt
      have hi₀_le : ω i₀ * (1 - α i₀) ≤ δ := by
        simpa [δ] using
          (Finset.single_le_sum
            (fun j _ ↦ mul_nonneg (hω j).1 (sub_nonneg.mpr (hα j).2.le))
            (by simp : i₀ ∈ (Finset.univ : Finset I)))
      exact lt_of_lt_of_le hi₀_pos hi₀_le
    have hsplit : αbar + δ = 1 := by
      calc
        αbar + δ = ∑ i, (ω i * α i + ω i * (1 - α i)) := by
          simp [αbar, δ, Finset.sum_add_distrib]
        _ = ∑ i, ω i := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          ring
        _ = 1 := hω_sum
    nlinarith
  exact ⟨hαbar_pos, hαbar_lt⟩

/-- Helper for Proposition 4.42: normalizing the coefficients `ω i * α i` by their positive total
produces convex weights. -/
private lemma normalized_companion_weights_mem_Icc (ω α : I → ℝ)
    (hω : ∀ i, ω i ∈ Set.Icc (0 : ℝ) 1) (hαi : ∀ i, α i ∈ Set.Ioo (0 : ℝ) 1)
    (hα : (∑ i, ω i * α i) ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ i, (ω i * α i) / (∑ j, ω j * α j) ∈ Set.Icc (0 : ℝ) 1 := by
  intro i
  have hαbar_pos : 0 < ∑ j, ω j * α j := hα.1
  have hnum_nonneg : 0 ≤ ω i * α i := mul_nonneg (hω i).1 (hαi i).1.le
  have hnum_le :
      ω i * α i ≤ ∑ j, ω j * α j := by
    simpa using
      (Finset.single_le_sum
        (fun j _ ↦ mul_nonneg (hω j).1 (hαi j).1.le)
        (by simp : i ∈ (Finset.univ : Finset I)))
  refine ⟨div_nonneg hnum_nonneg hαbar_pos.le, ?_⟩
  have hdiv_le :
      (ω i * α i) / (∑ j, ω j * α j) ≤
        (∑ j, ω j * α j) / (∑ j, ω j * α j) := by
    exact div_le_div_of_nonneg_right hnum_le hαbar_pos.le
  simpa [ne_of_gt hαbar_pos] using hdiv_le

/-- Helper for Proposition 4.42: the normalized coefficients of the affine companion sum to `1`. -/
private lemma normalized_companion_weights_sum (ω α : I → ℝ)
    (hα : (∑ i, ω i * α i) ∈ Set.Ioo (0 : ℝ) 1) :
    ∑ i, (ω i * α i) / (∑ j, ω j * α j) = 1 := by
  let αbar : ℝ := ∑ i, ω i * α i
  have hαbar_pos : 0 < αbar := by
    simpa [αbar] using hα.1
  have hαbar_ne : αbar ≠ 0 := ne_of_gt hαbar_pos
  calc
    ∑ i, (ω i * α i) / (∑ j, ω j * α j)
        = ∑ i, (ω i * α i) / αbar := by simp [αbar]
    _ = ∑ i, (ω i * α i) * αbar⁻¹ := by
          simp [div_eq_mul_inv]
    _ = (∑ i, ω i * α i) * αbar⁻¹ := by
          rw [← Finset.sum_mul]
    _ = αbar * αbar⁻¹ := by simp [αbar]
    _ = 1 := by
          exact mul_inv_cancel₀ hαbar_ne

/-- Helper for Proposition 4.42: a finite convex combination of `1`-Lipschitz maps on `D` is again
`1`-Lipschitz. -/
private lemma lipschitzWith_weighted_sum_fintype (β : I → ℝ) (R : I → D → H)
    (hR : ∀ i, LipschitzWith 1 (R i))
    (hβ : ∀ i, β i ∈ Set.Icc (0 : ℝ) 1) (hβ_sum : ∑ i, β i = 1) :
    LipschitzWith 1 (fun x : D ↦ ∑ i, β i • R i x) := by
  -- Control the weighted companion by the same triangle-inequality argument as Proposition 4.9.
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  calc
    dist (∑ i, β i • R i x) (∑ i, β i • R i y)
        = ‖∑ i, β i • (R i x - R i y)‖ := by
            simp [dist_eq_norm, smul_sub, Finset.sum_sub_distrib]
    _ ≤ ∑ i, ‖β i • (R i x - R i y)‖ := norm_sum_le _ _
    _ = ∑ i, β i * ‖R i x - R i y‖ := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hβ i).1]
    _ ≤ ∑ i, β i * dist x y := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have hRi : ‖R i x - R i y‖ ≤ dist x y := by
            simpa [dist_eq_norm] using (hR i).dist_le_mul x y
          exact mul_le_mul_of_nonneg_left hRi (hβ i).1
    _ = (∑ i, β i) * dist x y := by
          rw [Finset.sum_mul]
    _ = 1 * dist x y := by
          rw [hβ_sum]

/-- Helper for Proposition 4.42: after expanding each averaged operator, the weighted sum regroups
into the affine form with coefficient `∑ i, ω i * α i`. -/
private lemma weighted_sum_affine_decomposition (ω α : I → ℝ) (T R : I → D → H)
    (hω_sum : ∑ i, ω i = 1)
    (hα : (∑ i, ω i * α i) ∈ Set.Ioo (0 : ℝ) 1)
    (hTR : ∀ i, T i = fun x : D ↦ (1 - α i) • (x : H) + α i • R i x) :
    (fun x : D ↦ ∑ i, ω i • T i x) =
      fun x : D ↦
        (1 - ∑ i, ω i * α i) • (x : H) +
          (∑ i, ω i * α i) •
            (∑ i, ((ω i * α i) / (∑ j, ω j * α j)) • R i x) := by
  let αbar : ℝ := ∑ i, ω i * α i
  have hαbar_pos : 0 < αbar := by
    simpa [αbar] using hα.1
  have hαbar_ne : αbar ≠ 0 := ne_of_gt hαbar_pos
  have hcoeff :
      ∑ i, ω i * (1 - α i) = 1 - αbar := by
    calc
      ∑ i, ω i * (1 - α i)
          = ∑ i, (ω i - ω i * α i) := by
              refine Finset.sum_congr rfl fun i _ ↦ by ring
      _ = (∑ i, ω i) - ∑ i, ω i * α i := by
            rw [Finset.sum_sub_distrib]
      _ = 1 - αbar := by
            simp [hω_sum, αbar]
  -- Expand every `T i`, collect the identity part, and factor the companion part through `αbar`.
  ext x
  calc
    ∑ i, ω i • T i x
        = ∑ i, ω i • ((1 - α i) • (x : H) + α i • R i x) := by
            refine Finset.sum_congr rfl fun i _ ↦ by simp [hTR i]
    _ = ∑ i, ((ω i * (1 - α i)) • (x : H) + (ω i * α i) • R i x) := by
          refine Finset.sum_congr rfl fun i _ ↦ by
            rw [smul_add, ← mul_smul, ← mul_smul]
    _ = (∑ i, (ω i * (1 - α i)) • (x : H)) + ∑ i, (ω i * α i) • R i x := by
          rw [Finset.sum_add_distrib]
    _ = (∑ i, ω i * (1 - α i)) • (x : H) + ∑ i, (ω i * α i) • R i x := by
          rw [Finset.sum_smul]
    _ = (1 - αbar) • (x : H) + ∑ i, (ω i * α i) • R i x := by
          simp [hcoeff]
    _ = (1 - αbar) • (x : H) +
          αbar • (∑ i, ((ω i * α i) / αbar) • R i x) := by
          congr 1
          have hcomp :
              αbar • (∑ i, ((ω i * α i) / αbar) • R i x) =
                ∑ i, (ω i * α i) • R i x := by
            calc
              αbar • (∑ i, ((ω i * α i) / αbar) • R i x)
                  = ∑ i, (αbar * ((ω i * α i) / αbar)) • R i x := by
                      rw [Finset.smul_sum]
                      refine Finset.sum_congr rfl fun i _ ↦ by rw [smul_smul]
              _ = ∑ i, (ω i * α i) • R i x := by
                    refine Finset.sum_congr rfl fun i _ ↦ ?_
                    congr 1
                    field_simp [hαbar_ne]
          exact hcomp.symm
    _ = (1 - ∑ i, ω i * α i) • (x : H) +
          (∑ i, ω i * α i) •
            (∑ i, ((ω i * α i) / (∑ j, ω j * α j)) • R i x) := by
          simp [αbar]

-- Proof sketch: for each `i`, write `T i = (1 - α i) Id + α i R i` with `R i` nonexpansive.
-- Set `α := ∑ i, ω i * α i` and define `R := ∑ i, (ω i * α i / α) • R i`. The coefficients of `R`
-- are nonnegative and sum to `1`, so `R` is nonexpansive by the convex-combination result for
-- nonexpansive maps. Expanding the weighted sum of the `T i` then gives
-- `∑ i, ω i • T i = (1 - α) Id + α R`.
/-- Proposition 4.42: a finite convex combination of `α i`-averaged operators on a subset of a
real Hilbert space is `(\sum i, ω i * α i)`-averaged. -/
theorem averagedWith_weightedSum (ω α : I → ℝ) (T : I → D → H)
    (hω : ∀ i, ω i ∈ Set.Icc (0 : ℝ) 1) (hω_sum : ∑ i, ω i = 1)
    (hT : ∀ i, AveragedWith (α i) (T i)) :
    AveragedWith (∑ i, ω i * α i) (fun x : D ↦ ∑ i, ω i • T i x) := by
  have hαi : ∀ i, α i ∈ Set.Ioo (0 : ℝ) 1 := fun i ↦ (hT i).mem_Ioo
  have hαbar : (∑ i, ω i * α i) ∈ Set.Ioo (0 : ℝ) 1 :=
    weighted_averagingParameter_mem_Ioo ω α hω hω_sum hαi
  -- Write each `T i` with its nonexpansive affine companion.
  have hT' :
      ∀ i, ∃ R : D → H, LipschitzWith 1 R ∧
        T i = fun x : D ↦ (1 - α i) • (x : H) + α i • R x := by
    intro i
    exact (averagedWith_iff.mp (hT i)).2
  choose R hR hTR using hT'
  let β : I → ℝ := fun i ↦ (ω i * α i) / (∑ j, ω j * α j)
  let S : D → H := fun x ↦ ∑ i, β i • R i x
  have hβ : ∀ i, β i ∈ Set.Icc (0 : ℝ) 1 := by
    -- The normalized companion coefficients are convex weights.
    intro i
    simpa [β] using normalized_companion_weights_mem_Icc ω α hω hαi hαbar i
  have hβ_sum : ∑ i, β i = 1 := by
    -- The normalized companion coefficients sum to one.
    simpa [β] using normalized_companion_weights_sum ω α hαbar
  have hS_lipschitz : LipschitzWith 1 S := by
    -- A convex combination of nonexpansive companions stays nonexpansive.
    simpa [S, β] using lipschitzWith_weighted_sum_fintype β R hR hβ hβ_sum
  -- Route correction: use the normalized weighted companion directly, then regroup the affine
  -- expansion of the weighted sum into `(1 - αbar) Id + αbar S`.
  refine averagedWith_iff.mpr ⟨hαbar, S, hS_lipschitz, ?_⟩
  simpa [S, β] using weighted_sum_affine_decomposition ω α T R hω_sum hαbar hTR

end

/-! Source item: Chap04/Proposition_4_44 -/

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {D : Set H}

/-- The averaging constant attached to the composition of an `α₁`-averaged map with an
`α₂`-averaged map. -/
noncomputable def compositionAveragingConstant (α₁ α₂ : ℝ) : ℝ :=
  (α₁ + α₂ - 2 * α₁ * α₂) / (1 - α₁ * α₂)

/-- The composition averaging constant attached to two parameters in `(0, 1)` also lies in
`(0, 1)`. -/
theorem compositionAveragingConstant_mem_Ioo
    {α₁ α₂ : ℝ} (hα₁ : α₁ ∈ Set.Ioo (0 : ℝ) 1) (hα₂ : α₂ ∈ Set.Ioo (0 : ℝ) 1) :
    compositionAveragingConstant α₁ α₂ ∈ Set.Ioo (0 : ℝ) 1 := by
  have hdenom_pos : 0 < 1 - α₁ * α₂ := by
    nlinarith [hα₁.1, hα₁.2, hα₂.1, hα₂.2]
  have hnum_pos_aux : 0 < α₁ * (1 - α₂) + α₂ * (1 - α₁) := by
    nlinarith [hα₁.1, hα₁.2, hα₂.1, hα₂.2]
  have hnum_pos : 0 < α₁ + α₂ - 2 * α₁ * α₂ := by
    convert hnum_pos_aux using 1
    ring
  have hnum_lt_denom : α₁ + α₂ - 2 * α₁ * α₂ < 1 - α₁ * α₂ := by
    nlinarith [hα₁.1, hα₁.2, hα₂.1, hα₂.2]
  constructor
  · dsimp [compositionAveragingConstant]
    exact div_pos hnum_pos hdenom_pos
  · dsimp [compositionAveragingConstant]
    exact (div_lt_one hdenom_pos).2 hnum_lt_denom

/-- The affine-combination identity from Corollary 2.15 yields the lower bound used in the
composition argument. -/
private lemma weighted_sqnorm_ge_mul_norm_sub_sq (u v : H) (lam : ℝ) :
    lam * ‖u‖ ^ 2 + (1 - lam) * ‖v‖ ^ 2 ≥ lam * (1 - lam) * ‖u - v‖ ^ 2 := by
  have hidentity := norm_sq_affine_combination_add_weighted_norm_sub_sq u v lam
  have hnonneg : 0 ≤ ‖lam • u + (1 - lam) • v‖ ^ 2 := sq_nonneg _
  nlinarith [hidentity, hnonneg]

-- The two defect terms from the proof of Proposition 4.44 differ by the residual of `T₁ ∘ T₂`.
omit [InnerProductSpace ℝ H] in
private lemma composition_residual_eq_defect_sub_reverse_defect
    (T₁ T₂ : D → D) (x y : D) :
    (((T₂ x : H) - T₁ (T₂ x)) - ((T₂ y : H) - T₁ (T₂ y))) -
        (((y : H) - T₂ y) - ((x : H) - T₂ x)) =
      ((x : H) - T₁ (T₂ x)) - (y - T₁ (T₂ y)) := by
  simp [sub_eq_add_neg]
  abel_nf

/-- Proposition 4.44: the composition of two averaged self-maps is averaged, with averaging
constant `compositionAveragingConstant α₁ α₂`. -/
theorem averagedWith_comp {α₁ α₂ : ℝ} {T₁ T₂ : D → D}
    (hT₁ : AveragedWith α₁ (fun x : D ↦ (T₁ x : H)))
    (hT₂ : AveragedWith α₂ (fun x : D ↦ (T₂ x : H))) :
    AveragedWith (compositionAveragingConstant α₁ α₂) (fun x : D ↦ (T₁ (T₂ x) : H)) := by
  let α : ℝ := compositionAveragingConstant α₁ α₂
  let A : ℝ := (1 - α₁) / α₁
  let B : ℝ := (1 - α₂) / α₂
  let τ : ℝ := A + B
  have hα₁ : α₁ ∈ Set.Ioo (0 : ℝ) 1 := hT₁.mem_Ioo
  have hα₂ : α₂ ∈ Set.Ioo (0 : ℝ) 1 := hT₂.mem_Ioo
  have hα : α ∈ Set.Ioo (0 : ℝ) 1 := compositionAveragingConstant_mem_Ioo hα₁ hα₂
  have hA_pos : 0 < A := by
    dsimp [A]
    exact div_pos (sub_pos.mpr hα₁.2) hα₁.1
  have hB_pos : 0 < B := by
    dsimp [B]
    exact div_pos (sub_pos.mpr hα₂.2) hα₂.1
  have hτ_pos : 0 < τ := by
    dsimp [τ]
    linarith
  rw [averagedWith_iff_residual_sqnorm_ineq hα]
  intro x y
  let a : H := ((T₂ x : H) - T₁ (T₂ x)) - ((T₂ y : H) - T₁ (T₂ y))
  let b : H := ((y : H) - T₂ y) - ((x : H) - T₂ x)
  have hT₁ineq := (averagedWith_iff_residual_sqnorm_ineq hα₁).1 hT₁ (T₂ x) (T₂ y)
  have hT₁ineq' :
      ‖(T₁ (T₂ x) : H) - T₁ (T₂ y)‖ ^ 2 ≤ ‖(T₂ x : H) - T₂ y‖ ^ 2 - A * ‖a‖ ^ 2 := by
    simpa [A, a] using hT₁ineq
  have hT₂ineq := (averagedWith_iff_residual_sqnorm_ineq hα₂).1 hT₂ x y
  have hT₂ineq' :
      ‖(T₂ x : H) - T₂ y‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2 - B * ‖b‖ ^ 2 := by
    have hb_eq :
        b = - (((x : H) - T₂ x) - (y - T₂ y)) := by
      simp [b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    calc
      ‖(T₂ x : H) - T₂ y‖ ^ 2
          ≤ ‖(x : H) - y‖ ^ 2 - B * ‖((x : H) - T₂ x) - (y - T₂ y)‖ ^ 2 := by
            simpa [B] using hT₂ineq
      _ = ‖(x : H) - y‖ ^ 2 - B * ‖b‖ ^ 2 := by
            rw [hb_eq, norm_neg]
  have hsum :
      ‖(T₁ (T₂ x) : H) - T₁ (T₂ y)‖ ^ 2 ≤
        ‖(x : H) - y‖ ^ 2 - A * ‖a‖ ^ 2 - B * ‖b‖ ^ 2 := by
    nlinarith [hT₁ineq', hT₂ineq']
  have hLam_mem : A / τ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact le_of_lt (div_pos hA_pos hτ_pos)
    · have hA_le_τ : A ≤ τ := by
        dsimp [τ]
        linarith [le_of_lt hB_pos]
      have hτ_ne : τ ≠ 0 := ne_of_gt hτ_pos
      have hdiv : A / τ ≤ 1 := by
        field_simp [hτ_ne]
        exact hA_le_τ
      exact hdiv
  have hweighted :
      (A / τ) * (1 - A / τ) * ‖a - b‖ ^ 2 ≤
        (A / τ) * ‖a‖ ^ 2 + (1 - A / τ) * ‖b‖ ^ 2 := by
    simpa using weighted_sqnorm_ge_mul_norm_sub_sq a b (A / τ)
  have hτ_ne : τ ≠ 0 := ne_of_gt hτ_pos
  have hone_sub : 1 - A / τ = B / τ := by
    field_simp [hτ_ne]
    dsimp [τ]
    ring
  have hweighted' :
      (A / τ) * (B / τ) * ‖a - b‖ ^ 2 ≤
        (A / τ) * ‖a‖ ^ 2 + (B / τ) * ‖b‖ ^ 2 := by
    simpa [hone_sub] using hweighted
  have hmerge :
      (A * B / τ) * ‖a - b‖ ^ 2 ≤ A * ‖a‖ ^ 2 + B * ‖b‖ ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hweighted' (le_of_lt hτ_pos)
    have hleft :
        τ * ((A / τ) * (B / τ) * ‖a - b‖ ^ 2) = (A * B / τ) * ‖a - b‖ ^ 2 := by
      field_simp [hτ_ne]
    have hright :
        τ * ((A / τ) * ‖a‖ ^ 2 + (B / τ) * ‖b‖ ^ 2) = A * ‖a‖ ^ 2 + B * ‖b‖ ^ 2 := by
      field_simp [hτ_ne]
    rw [hleft, hright] at hmul
    exact hmul
  have hresidual :
      a - b = ((x : H) - T₁ (T₂ x)) - (y - T₁ (T₂ y)) := by
    simpa [a, b] using composition_residual_eq_defect_sub_reverse_defect T₁ T₂ x y
  have hcoeff :
      A * B / τ = (1 - α) / α := by
    have hα₁_ne : α₁ ≠ 0 := ne_of_gt hα₁.1
    have hα₂_ne : α₂ ≠ 0 := ne_of_gt hα₂.1
    have hdenom_ne : 1 - α₁ * α₂ ≠ 0 := by
      nlinarith [hα₁.1, hα₁.2, hα₂.1, hα₂.2]
    dsimp [A, B, τ, α, compositionAveragingConstant]
    field_simp [hα₁_ne, hα₂_ne, hdenom_ne]
    ring
  have hresidual_control :
      ((1 - α) / α) * ‖((x : H) - T₁ (T₂ x)) - (y - T₁ (T₂ y))‖ ^ 2 ≤
        A * ‖a‖ ^ 2 + B * ‖b‖ ^ 2 := by
    calc
      ((1 - α) / α) * ‖((x : H) - T₁ (T₂ x)) - (y - T₁ (T₂ y))‖ ^ 2
          = (A * B / τ) * ‖a - b‖ ^ 2 := by
            rw [← hcoeff, ← hresidual]
      _ ≤ A * ‖a‖ ^ 2 + B * ‖b‖ ^ 2 := hmerge
  have htarget :
      ‖(T₁ (T₂ x) : H) - T₁ (T₂ y)‖ ^ 2 ≤
        ‖(x : H) - y‖ ^ 2 -
          ((1 - α) / α) * ‖((x : H) - T₁ (T₂ x)) - (y - T₁ (T₂ y))‖ ^ 2 := by
    nlinarith [hsum, hresidual_control]
  simpa [α] using htarget

end
