import Mathlib
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.ext_def_1

open scoped InnerProductSpace

namespace Nesterov1983

/-- The descent estimate for a function with `L`-Lipschitz gradient. -/
theorem descent_lemma {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (L : ℝ) (h : IsC11 f L) (x y : E) :
    f y ≤ f x + inner ℝ (gradient f x) (y - x) + (L / 2) * ‖y - x‖ ^ 2 := by
  let φ : ℝ → E := fun t => AffineMap.lineMap x y t
  let r : ℝ → ℝ := fun t =>
    f (φ t) - f x - t * inner ℝ (gradient f x) (y - x) -
      (L / 2) * t ^ 2 * ‖y - x‖ ^ 2
  have hr0 : r 0 = 0 := by
    simp [r, φ]
  have hline_f (t₀ : ℝ) :
      HasDerivAt (fun t : ℝ => f (φ t))
        (inner ℝ (gradient f (φ t₀)) (y - x)) t₀ := by
    have hline : HasDerivAt φ (y - x) t₀ := by
      simpa [φ] using
        (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t₀))
    have hcomp := (h.hasGradientAt (φ t₀)).hasFDerivAt.comp_hasDerivAt t₀ hline
    simpa using hcomp
  have hr_deriv (t : ℝ) :
      HasDerivAt r
        (inner ℝ (gradient f (φ t) - gradient f x) (y - x) - L * t * ‖y - x‖ ^ 2) t := by
    have h1 : HasDerivAt (fun s : ℝ => f (φ s))
        (inner ℝ (gradient f (φ t)) (y - x)) t := hline_f t
    have h2 : HasDerivAt (fun _ : ℝ => f x) 0 t := hasDerivAt_const t (f x)
    have h3 : HasDerivAt (fun s : ℝ => s * inner ℝ (gradient f x) (y - x))
        (inner ℝ (gradient f x) (y - x)) t := by
      simpa using
        (hasDerivAt_id t |>.mul_const (inner ℝ (gradient f x) (y - x)))
    have h4 : HasDerivAt (fun s : ℝ => (L / 2) * s ^ 2 * ‖y - x‖ ^ 2)
        (L * t * ‖y - x‖ ^ 2) t := by
      have hs : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa [Nat.cast_ofNat] using hasDerivAt_pow 2 t
      convert (hs.const_mul (L / 2)).mul_const (‖y - x‖ ^ 2) using 1
      ring
    have hderiv := ((h1.sub h2).sub h3).sub h4
    simpa [r, sub_sub, inner_sub_left] using hderiv
  have hr_diff (t : ℝ) : DifferentiableAt ℝ r t :=
    (hr_deriv t).differentiableAt
  have hr_cont : Continuous r :=
    continuous_iff_continuousAt.mpr fun t => (hr_diff t).continuousAt
  have hr_contOn : ContinuousOn r (Set.Icc (0 : ℝ) 1) := hr_cont.continuousOn
  have hr_diffOn : DifferentiableOn ℝ r (Set.Ioo (0 : ℝ) 1) :=
    fun t _ => (hr_diff t).differentiableWithinAt
  have hr_deriv_nonpos {t : ℝ} (ht : 0 < t) :
      inner ℝ (gradient f (φ t) - gradient f x) (y - x) - L * t * ‖y - x‖ ^ 2 ≤ 0 := by
    have h_cauchy :
        inner ℝ (gradient f (φ t) - gradient f x) (y - x) ≤
          ‖gradient f (φ t) - gradient f x‖ * ‖y - x‖ :=
      real_inner_le_norm _ _
    have h_lip : ‖gradient f (φ t) - gradient f x‖ ≤ L * ‖φ t - x‖ :=
      h.lipschitz (φ t) x
    have h_norm_φ : ‖φ t - x‖ = t * ‖y - x‖ := by
      have hdist : dist x (AffineMap.lineMap x y t) = ‖t‖ * dist x y :=
        dist_left_lineMap x y t
      have htnorm : ‖t‖ = t := abs_of_pos ht
      simpa [φ, dist_eq_norm, norm_sub_rev, htnorm, mul_comm] using hdist
    have h_inner_bound :
        inner ℝ (gradient f (φ t) - gradient f x) (y - x) ≤ L * t * ‖y - x‖ ^ 2 := by
      calc
        inner ℝ (gradient f (φ t) - gradient f x) (y - x)
            ≤ ‖gradient f (φ t) - gradient f x‖ * ‖y - x‖ := h_cauchy
        _ ≤ (L * ‖φ t - x‖) * ‖y - x‖ := by
          nlinarith [h_lip, norm_nonneg (y - x)]
        _ = L * t * ‖y - x‖ ^ 2 := by
          rw [h_norm_φ]
          ring
    linarith
  have h_mvt : ∃ c ∈ Set.Ioo (0 : ℝ) 1,
      deriv r c = (r 1 - r 0) / (1 - 0) :=
    exists_deriv_eq_slope r (by norm_num : (0 : ℝ) < 1) hr_contOn hr_diffOn
  rcases h_mvt with ⟨c, hc, hc_eq⟩
  have h_deriv_c : deriv r c =
      inner ℝ (gradient f (φ c) - gradient f x) (y - x) - L * c * ‖y - x‖ ^ 2 :=
    (hr_deriv c).deriv
  have h_deriv_c_nonpos : deriv r c ≤ 0 := by
    rw [h_deriv_c]
    exact hr_deriv_nonpos hc.1
  rw [show (1 : ℝ) - 0 = 1 by norm_num, div_one, hr0, sub_zero] at hc_eq
  have hr1_nonpos : r 1 ≤ 0 := by linarith
  simp [r, φ] at hr1_nonpos
  linarith

end Nesterov1983
