import Mathlib

namespace AttouchPeypouquetRedont2014

/-- Descent inequality for a differentiable function with an `L`-Lipschitz gradient. -/
theorem descent_lemma {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (psi : H → ℝ) (gradPsi : H → H) (L : ℝ) (hdiff : Differentiable ℝ psi)
    (hgrad : ∀ x h, fderiv ℝ psi x h = inner ℝ (gradPsi x) h)
    (hlip : ∀ x y, ‖gradPsi x - gradPsi y‖ ≤ L * ‖x - y‖) (x v : H) :
    psi v ≤ psi x + inner ℝ (gradPsi x) (v - x) + L / 2 * ‖v - x‖ ^ 2 := by
  let φ : ℝ → H := fun t => AffineMap.lineMap x v t
  let r : ℝ → ℝ := fun t =>
    psi (φ t) - psi x - t * inner ℝ (gradPsi x) (v - x) -
      (L / 2) * t ^ 2 * ‖v - x‖ ^ 2
  have hr0 : r 0 = 0 := by
    simp [r, φ]
  have hline_psi (t₀ : ℝ) :
      HasDerivAt (fun t : ℝ => psi (φ t))
        (inner ℝ (gradPsi (φ t₀)) (v - x)) t₀ := by
    have hline : HasDerivAt φ (v - x) t₀ := by
      simpa [φ] using
        (AffineMap.hasDerivAt_lineMap (a := x) (b := v) (x := t₀))
    have hcomp := (hdiff (φ t₀)).hasFDerivAt.comp_hasDerivAt t₀ hline
    rw [hgrad (φ t₀) (v - x)] at hcomp
    exact hcomp
  have hr_deriv (t : ℝ) :
      HasDerivAt r
        (inner ℝ (gradPsi (φ t) - gradPsi x) (v - x) - L * t * ‖v - x‖ ^ 2) t := by
    have h1 : HasDerivAt (fun s : ℝ => psi (φ s))
        (inner ℝ (gradPsi (φ t)) (v - x)) t := hline_psi t
    have h2 : HasDerivAt (fun _ : ℝ => psi x) 0 t := hasDerivAt_const t (psi x)
    have h3 : HasDerivAt (fun s : ℝ => s * inner ℝ (gradPsi x) (v - x))
        (inner ℝ (gradPsi x) (v - x)) t := by
      simpa using
        (hasDerivAt_id t |>.mul_const (inner ℝ (gradPsi x) (v - x)))
    have h4 : HasDerivAt (fun s : ℝ => (L / 2) * s ^ 2 * ‖v - x‖ ^ 2)
        (L * t * ‖v - x‖ ^ 2) t := by
      have hs : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa [Nat.cast_ofNat] using hasDerivAt_pow 2 t
      convert (hs.const_mul (L / 2)).mul_const (‖v - x‖ ^ 2) using 1
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
      inner ℝ (gradPsi (φ t) - gradPsi x) (v - x) - L * t * ‖v - x‖ ^ 2 ≤ 0 := by
    have h_cauchy :
        inner ℝ (gradPsi (φ t) - gradPsi x) (v - x) ≤
          ‖gradPsi (φ t) - gradPsi x‖ * ‖v - x‖ :=
      real_inner_le_norm _ _
    have h_lip : ‖gradPsi (φ t) - gradPsi x‖ ≤ L * ‖φ t - x‖ :=
      hlip (φ t) x
    have h_norm_φ : ‖φ t - x‖ = t * ‖v - x‖ := by
      have hdist : dist x (AffineMap.lineMap x v t) = ‖t‖ * dist x v :=
        dist_left_lineMap x v t
      have htnorm : ‖t‖ = t := abs_of_pos ht
      simpa [φ, dist_eq_norm, norm_sub_rev, htnorm, mul_comm] using hdist
    have h_inner_bound :
        inner ℝ (gradPsi (φ t) - gradPsi x) (v - x) ≤ L * t * ‖v - x‖ ^ 2 := by
      calc
        inner ℝ (gradPsi (φ t) - gradPsi x) (v - x)
            ≤ ‖gradPsi (φ t) - gradPsi x‖ * ‖v - x‖ := h_cauchy
        _ ≤ (L * ‖φ t - x‖) * ‖v - x‖ := by
          nlinarith [h_lip, norm_nonneg (v - x)]
        _ = L * t * ‖v - x‖ ^ 2 := by
          rw [h_norm_φ]
          ring
    linarith
  have h_mvt : ∃ c ∈ Set.Ioo (0 : ℝ) 1,
      deriv r c = (r 1 - r 0) / (1 - 0) :=
    exists_deriv_eq_slope r (by norm_num : (0 : ℝ) < 1) hr_contOn hr_diffOn
  rcases h_mvt with ⟨c, hc, hc_eq⟩
  have h_deriv_c : deriv r c =
      inner ℝ (gradPsi (φ c) - gradPsi x) (v - x) - L * c * ‖v - x‖ ^ 2 :=
    (hr_deriv c).deriv
  have h_deriv_c_nonpos : deriv r c ≤ 0 := by
    rw [h_deriv_c]
    exact hr_deriv_nonpos hc.1
  rw [show (1 : ℝ) - 0 = 1 by norm_num, div_one, hr0, sub_zero] at hc_eq
  have hr1_nonpos : r 1 ≤ 0 := by linarith
  simp [r, φ] at hr1_nonpos
  linarith

end AttouchPeypouquetRedont2014
