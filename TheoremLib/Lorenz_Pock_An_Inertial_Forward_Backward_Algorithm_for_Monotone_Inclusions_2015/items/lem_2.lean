import Mathlib
import Foundation.Hilbert.Basic
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.ext_def_1

namespace LorenzPock

private theorem block_young_lower_bound (r a b t : ℝ) (hr0 : 0 ≤ r)
    (ht : -(r * a * b) ≤ t) :
    (1 - r) * (a ^ 2 + b ^ 2) ≤ a ^ 2 + 2 * t + b ^ 2 := by
  nlinarith [mul_nonneg hr0 (sq_nonneg (a - b))]

/-- The off-diagonal term of the block operator, written through the square-root
factorisation: `⟪B x, y⟫ = ⟪(A₂^{-1/2} B A₁^{-1/2})(A₁^{1/2} x), A₂^{1/2} y⟫`.

Together with `⟪A₁ x, x⟫ = ‖A₁^{1/2} x‖²` this is what turns the block quadratic form into the
form `‖A₁^{1/2}x‖² + 2⟪T(A₁^{1/2}x), A₂^{1/2}y⟫ + ‖A₂^{1/2}y‖²` estimated in Lemma 8. -/
theorem block_operator_cross_term {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] (B : X →L[ℝ] Y) (A₁sqrt A₁invsqrt : X →L[ℝ] X)
    (A₂sqrt A₂invsqrt : Y →L[ℝ] Y)
    (hA₁invsqrt : A₁invsqrt.comp A₁sqrt = ContinuousLinearMap.id ℝ X)
    (hA₂invsqrt : A₂invsqrt.comp A₂sqrt = ContinuousLinearMap.id ℝ Y)
    (hA₂invsqrt_selfadjoint : ∀ x y, inner ℝ (A₂invsqrt x) y = inner ℝ x (A₂invsqrt y))
    (x : X) (y : Y) :
    inner ℝ (B x) y = inner ℝ ((A₂invsqrt.comp (B.comp A₁invsqrt)) (A₁sqrt x)) (A₂sqrt y) := by
  have hA₁inv_apply (w : X) : A₁invsqrt (A₁sqrt w) = w := by
    have h := congrArg (fun L : X →L[ℝ] X => L w) hA₁invsqrt
    simpa [ContinuousLinearMap.comp_apply] using h
  have hA₂inv_apply (w : Y) : A₂invsqrt (A₂sqrt w) = w := by
    have h := congrArg (fun L : Y →L[ℝ] Y => L w) hA₂invsqrt
    simpa [ContinuousLinearMap.comp_apply] using h
  change inner ℝ (B x) y = inner ℝ (A₂invsqrt (B (A₁invsqrt (A₁sqrt x)))) (A₂sqrt y)
  rw [hA₁inv_apply, hA₂invsqrt_selfadjoint, hA₂inv_apply]

/-- Lemma 8: a block operator is positive definite under the stated Schur-type norm bound. -/
theorem block_operator_positive_definite {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y]
    (A₁ : X →L[ℝ] X) (A₂ : Y →L[ℝ] Y) (B : X →L[ℝ] Y)
    (hsymm₁ : ∀ x y, inner ℝ (A₁ x) y = inner ℝ x (A₁ y))
    (hsymm₂ : ∀ x y, inner ℝ (A₂ x) y = inner ℝ x (A₂ y))
    (hpos₁ : ∀ x ≠ 0, 0 < inner ℝ (A₁ x) x)
    (hpos₂ : ∀ y ≠ 0, 0 < inner ℝ (A₂ y) y)
    (A₁sqrt A₁invsqrt : X →L[ℝ] X) (A₂sqrt A₂invsqrt : Y →L[ℝ] Y)
    (hA₁sqrt : A₁sqrt.comp A₁sqrt = A₁)
    (hA₂sqrt : A₂sqrt.comp A₂sqrt = A₂)
    (hA₁invsqrt : A₁invsqrt.comp A₁sqrt = ContinuousLinearMap.id ℝ X)
    (hA₂invsqrt : A₂invsqrt.comp A₂sqrt = ContinuousLinearMap.id ℝ Y)
    (hA₁sqrt_selfadjoint : ∀ x y, inner ℝ (A₁sqrt x) y = inner ℝ x (A₁sqrt y))
    (hA₂sqrt_selfadjoint : ∀ x y, inner ℝ (A₂sqrt x) y = inner ℝ x (A₂sqrt y))
    (hA₂invsqrt_selfadjoint : ∀ x y, inner ℝ (A₂invsqrt x) y = inner ℝ x (A₂invsqrt y))
    (hA₁sqrt_positive : ∀ x, 0 ≤ inner ℝ (A₁sqrt x) x)
    (hA₂sqrt_positive : ∀ y, 0 ≤ inner ℝ (A₂sqrt y) y)
    (hA₂invsqrt_positive : ∀ y, 0 ≤ inner ℝ (A₂invsqrt y) y)
    (hbound : ‖A₂invsqrt.comp (B.comp A₁invsqrt)‖ < 1) :
    ∀ z : X × Y, z ≠ 0 →
      0 < inner ℝ (A₁ z.1 + B.adjoint z.2) z.1 + inner ℝ (B z.1 + A₂ z.2) z.2 := by
  intro z hz
  rcases z with ⟨x, y⟩
  dsimp at hz ⊢
  let T : X →L[ℝ] Y := A₂invsqrt.comp (B.comp A₁invsqrt)
  have hA₁inv_apply (w : X) : A₁invsqrt (A₁sqrt w) = w := by
    have h := congrArg (fun L : X →L[ℝ] X => L w) hA₁invsqrt
    simpa [ContinuousLinearMap.comp_apply] using h
  have hA₂inv_apply (w : Y) : A₂invsqrt (A₂sqrt w) = w := by
    have h := congrArg (fun L : Y →L[ℝ] Y => L w) hA₂invsqrt
    simpa [ContinuousLinearMap.comp_apply] using h
  have hdiag₁ : inner ℝ (A₁ x) x = ‖A₁sqrt x‖ ^ 2 := by
    calc
      inner ℝ (A₁ x) x = inner ℝ ((A₁sqrt.comp A₁sqrt) x) x := by rw [hA₁sqrt]
      _ = inner ℝ (A₁sqrt (A₁sqrt x)) x := by rfl
      _ = inner ℝ (A₁sqrt x) (A₁sqrt x) := hA₁sqrt_selfadjoint _ _
      _ = ‖A₁sqrt x‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hdiag₂ : inner ℝ (A₂ y) y = ‖A₂sqrt y‖ ^ 2 := by
    calc
      inner ℝ (A₂ y) y = inner ℝ ((A₂sqrt.comp A₂sqrt) y) y := by rw [hA₂sqrt]
      _ = inner ℝ (A₂sqrt (A₂sqrt y)) y := by rfl
      _ = inner ℝ (A₂sqrt y) (A₂sqrt y) := hA₂sqrt_selfadjoint _ _
      _ = ‖A₂sqrt y‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hcross : inner ℝ (B x) y = inner ℝ (T (A₁sqrt x)) (A₂sqrt y) := by
    change inner ℝ (B x) y =
      inner ℝ (A₂invsqrt (B (A₁invsqrt (A₁sqrt x)))) (A₂sqrt y)
    rw [hA₁inv_apply]
    rw [hA₂invsqrt_selfadjoint]
    rw [hA₂inv_apply]
  have hquad :
      inner ℝ (A₁ x + B.adjoint y) x + inner ℝ (B x + A₂ y) y =
        ‖A₁sqrt x‖ ^ 2 + 2 * inner ℝ (T (A₁sqrt x)) (A₂sqrt y) + ‖A₂sqrt y‖ ^ 2 := by
    rw [inner_add_left, inner_add_left, hdiag₁, hdiag₂, ← hcross]
    rw [B.adjoint_inner_left]
    rw [real_inner_comm y (B x)]
    ring
  have hinner : -(‖T‖ * ‖A₁sqrt x‖ * ‖A₂sqrt y‖) ≤
      inner ℝ (T (A₁sqrt x)) (A₂sqrt y) := by
    have hcs := real_inner_le_norm (-(T (A₁sqrt x))) (A₂sqrt y)
    have hop := T.le_opNorm (A₁sqrt x)
    have hmul : ‖-(T (A₁sqrt x))‖ * ‖A₂sqrt y‖ ≤
        (‖T‖ * ‖A₁sqrt x‖) * ‖A₂sqrt y‖ :=
      mul_le_mul_of_nonneg_right (by simpa using hop) (norm_nonneg _)
    rw [norm_neg] at hcs
    rw [norm_neg] at hmul
    rw [inner_neg_left] at hcs
    nlinarith
  have hlower :
      (1 - ‖T‖) * (‖A₁sqrt x‖ ^ 2 + ‖A₂sqrt y‖ ^ 2) ≤
        ‖A₁sqrt x‖ ^ 2 + 2 * inner ℝ (T (A₁sqrt x)) (A₂sqrt y) + ‖A₂sqrt y‖ ^ 2 :=
    block_young_lower_bound _ _ _ _ (norm_nonneg _) hinner
  have hsumpos : 0 < ‖A₁sqrt x‖ ^ 2 + ‖A₂sqrt y‖ ^ 2 := by
    by_cases hx : x = 0
    · have hy : y ≠ 0 := by
        intro hy
        apply hz
        simp [hx, hy]
      have hsqrt : A₂sqrt y ≠ 0 := by
        intro hs
        have hzero : A₂ y = 0 := by
          rw [← hA₂sqrt]
          simp [ContinuousLinearMap.comp_apply, hs]
        have := hpos₂ y hy
        rw [hzero] at this
        simpa using this
      rw [hx]
      simp only [map_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add]
      exact sq_pos_of_pos (norm_pos_iff.mpr hsqrt)
    · have hsqrt : A₁sqrt x ≠ 0 := by
        intro hs
        have hzero : A₁ x = 0 := by
          rw [← hA₁sqrt]
          simp [ContinuousLinearMap.comp_apply, hs]
        have := hpos₁ x hx
        rw [hzero] at this
        simpa using this
      exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (norm_pos_iff.mpr hsqrt)) (sq_nonneg _)
  rw [hquad]
  exact lt_of_lt_of_le (mul_pos (sub_pos.mpr hbound) hsumpos) hlower

/-- Lemma 8's estimate in quantitative form: if the two diagonal blocks are coercive with
constants `a`, `b`, then the block operator is coercive with constant
`(1 - ‖A₂^{-1/2} B A₁^{-1/2}‖) · min a b`.

This is the form used in §3.2: Theorem 1 needs not only the positivity of `S = M - ½C`
supplied by Lemma 8, but also a uniform lower bound for its quadratic form in order to pass
between the `S`-norm and the ambient norm (see the docstring of `thm_1`). -/
theorem block_operator_coercive_of_coercive_blocks {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y]
    (A₁ : X →L[ℝ] X) (A₂ : Y →L[ℝ] Y) (B : X →L[ℝ] Y)
    (A₁sqrt A₁invsqrt : X →L[ℝ] X) (A₂sqrt A₂invsqrt : Y →L[ℝ] Y)
    (hA₁sqrt : A₁sqrt.comp A₁sqrt = A₁)
    (hA₂sqrt : A₂sqrt.comp A₂sqrt = A₂)
    (hA₁invsqrt : A₁invsqrt.comp A₁sqrt = ContinuousLinearMap.id ℝ X)
    (hA₂invsqrt : A₂invsqrt.comp A₂sqrt = ContinuousLinearMap.id ℝ Y)
    (hA₁sqrt_selfadjoint : ∀ x y, inner ℝ (A₁sqrt x) y = inner ℝ x (A₁sqrt y))
    (hA₂sqrt_selfadjoint : ∀ x y, inner ℝ (A₂sqrt x) y = inner ℝ x (A₂sqrt y))
    (hA₂invsqrt_selfadjoint : ∀ x y, inner ℝ (A₂invsqrt x) y = inner ℝ x (A₂invsqrt y))
    (hcoerc₁ : ∃ a : ℝ, 0 < a ∧ ∀ x, a * ‖x‖ ^ 2 ≤ inner ℝ (A₁ x) x)
    (hcoerc₂ : ∃ b : ℝ, 0 < b ∧ ∀ y, b * ‖y‖ ^ 2 ≤ inner ℝ (A₂ y) y)
    (hbound : ‖A₂invsqrt.comp (B.comp A₁invsqrt)‖ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : X × Y, c * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) ≤
      inner ℝ (A₁ z.1 + B.adjoint z.2) z.1 + inner ℝ (B z.1 + A₂ z.2) z.2 := by
  obtain ⟨a, ha_pos, ha⟩ := hcoerc₁
  obtain ⟨b, hb_pos, hb⟩ := hcoerc₂
  let T : X →L[ℝ] Y := A₂invsqrt.comp (B.comp A₁invsqrt)
  have hT_lt : ‖T‖ < 1 := hbound
  refine ⟨(1 - ‖T‖) * min a b, mul_pos (sub_pos.mpr hT_lt) (lt_min ha_pos hb_pos), ?_⟩
  rintro ⟨x, y⟩
  have hA₁inv_apply (w : X) : A₁invsqrt (A₁sqrt w) = w := by
    have h := congrArg (fun L : X →L[ℝ] X => L w) hA₁invsqrt
    simpa [ContinuousLinearMap.comp_apply] using h
  have hA₂inv_apply (w : Y) : A₂invsqrt (A₂sqrt w) = w := by
    have h := congrArg (fun L : Y →L[ℝ] Y => L w) hA₂invsqrt
    simpa [ContinuousLinearMap.comp_apply] using h
  have hdiag₁ : inner ℝ (A₁ x) x = ‖A₁sqrt x‖ ^ 2 := by
    calc
      inner ℝ (A₁ x) x = inner ℝ ((A₁sqrt.comp A₁sqrt) x) x := by rw [hA₁sqrt]
      _ = inner ℝ (A₁sqrt (A₁sqrt x)) x := by rfl
      _ = inner ℝ (A₁sqrt x) (A₁sqrt x) := hA₁sqrt_selfadjoint _ _
      _ = ‖A₁sqrt x‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hdiag₂ : inner ℝ (A₂ y) y = ‖A₂sqrt y‖ ^ 2 := by
    calc
      inner ℝ (A₂ y) y = inner ℝ ((A₂sqrt.comp A₂sqrt) y) y := by rw [hA₂sqrt]
      _ = inner ℝ (A₂sqrt (A₂sqrt y)) y := by rfl
      _ = inner ℝ (A₂sqrt y) (A₂sqrt y) := hA₂sqrt_selfadjoint _ _
      _ = ‖A₂sqrt y‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hcross : inner ℝ (B x) y = inner ℝ (T (A₁sqrt x)) (A₂sqrt y) := by
    change inner ℝ (B x) y = inner ℝ (A₂invsqrt (B (A₁invsqrt (A₁sqrt x)))) (A₂sqrt y)
    rw [hA₁inv_apply, hA₂invsqrt_selfadjoint, hA₂inv_apply]
  have hquad : inner ℝ (A₁ x + B.adjoint y) x + inner ℝ (B x + A₂ y) y =
      ‖A₁sqrt x‖ ^ 2 + 2 * inner ℝ (T (A₁sqrt x)) (A₂sqrt y) + ‖A₂sqrt y‖ ^ 2 := by
    rw [inner_add_left, inner_add_left, hdiag₁, hdiag₂, ← hcross]
    rw [B.adjoint_inner_left]
    rw [real_inner_comm y (B x)]
    ring
  have hinner : -(‖T‖ * ‖A₁sqrt x‖ * ‖A₂sqrt y‖) ≤
      inner ℝ (T (A₁sqrt x)) (A₂sqrt y) := by
    have hcs := real_inner_le_norm (-(T (A₁sqrt x))) (A₂sqrt y)
    have hop := T.le_opNorm (A₁sqrt x)
    have hmul : ‖-(T (A₁sqrt x))‖ * ‖A₂sqrt y‖ ≤
        (‖T‖ * ‖A₁sqrt x‖) * ‖A₂sqrt y‖ :=
      mul_le_mul_of_nonneg_right (by simpa using hop) (norm_nonneg _)
    rw [norm_neg] at hcs
    rw [norm_neg] at hmul
    rw [inner_neg_left] at hcs
    nlinarith
  have hlower : (1 - ‖T‖) * (‖A₁sqrt x‖ ^ 2 + ‖A₂sqrt y‖ ^ 2) ≤
      ‖A₁sqrt x‖ ^ 2 + 2 * inner ℝ (T (A₁sqrt x)) (A₂sqrt y) + ‖A₂sqrt y‖ ^ 2 :=
    block_young_lower_bound _ _ _ _ (norm_nonneg _) hinner
  have hmin : min a b * (‖x‖ ^ 2 + ‖y‖ ^ 2) ≤ ‖A₁sqrt x‖ ^ 2 + ‖A₂sqrt y‖ ^ 2 := by
    have h1 : a * ‖x‖ ^ 2 ≤ ‖A₁sqrt x‖ ^ 2 := by rw [← hdiag₁]; exact ha x
    have h2 : b * ‖y‖ ^ 2 ≤ ‖A₂sqrt y‖ ^ 2 := by rw [← hdiag₂]; exact hb y
    rw [mul_add]
    exact add_le_add
      (le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)) h1)
      (le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)) h2)
  rw [hquad]
  calc (1 - ‖T‖) * min a b * (‖x‖ ^ 2 + ‖y‖ ^ 2)
      = (1 - ‖T‖) * (min a b * (‖x‖ ^ 2 + ‖y‖ ^ 2)) := by ring
    _ ≤ (1 - ‖T‖) * (‖A₁sqrt x‖ ^ 2 + ‖A₂sqrt y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmin (le_of_lt (sub_pos.mpr hT_lt))
    _ ≤ ‖A₁sqrt x‖ ^ 2 + 2 * inner ℝ (T (A₁sqrt x)) (A₂sqrt y) + ‖A₂sqrt y‖ ^ 2 := hlower

end LorenzPock
