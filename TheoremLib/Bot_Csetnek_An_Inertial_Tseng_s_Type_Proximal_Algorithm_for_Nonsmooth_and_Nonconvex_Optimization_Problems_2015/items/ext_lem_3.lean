import Mathlib
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.ext_def_1

namespace BotCsetnek2015

/-- Lemma 3.1: the descent lemma for a differentiable function with Lipschitz gradient. -/
theorem lemma_3_1_descent {m : Nat} (h : EuclideanSpace m -> Real) (L : Real)
    (hL : HasLipschitzContinuousGradient h L) :
    ∀ x y : EuclideanSpace m,
      h y <= h x + inner Real (gradient h x) (y - x) + (L / 2) * ‖y - x‖ ^ 2 := by
  intro x y
  let φ : Real -> EuclideanSpace m := fun t => AffineMap.lineMap x y t
  let q : Real -> Real := fun t =>
    h (φ t) - h x - t * inner Real (gradient h x) (y - x) -
      (L / 2) * t ^ 2 * ‖y - x‖ ^ 2
  have hq0 : q 0 = 0 := by
    simp [q, φ]
  have h_deriv (t₀ : Real) :
      HasDerivAt (fun t : Real => h (φ t))
        (inner Real (gradient h (φ t₀)) (y - x)) t₀ := by
    have hh_diffAt : DifferentiableAt Real h (φ t₀) := hL.2.1.differentiableAt
    have hline : HasDerivAt φ (y - x) t₀ := by
      simpa [φ] using
        (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t₀))
    have hcomp :
        HasDerivAt (fun t : Real => h (φ t)) ((fderiv Real h (φ t₀)) (y - x)) t₀ :=
      hh_diffAt.hasFDerivAt.comp_hasDerivAt t₀ hline
    have hgrad :
        (fderiv Real h (φ t₀)) (y - x) =
          inner Real (gradient h (φ t₀)) (y - x) := by
      exact (inner_gradient_left hh_diffAt).symm
    simpa [hgrad] using hcomp
  have hq_deriv (t : Real) :
      HasDerivAt q
        (inner Real (gradient h (φ t) - gradient h x) (y - x) -
          L * t * ‖y - x‖ ^ 2) t := by
    have h1 : HasDerivAt (fun s : Real => h (φ s))
        (inner Real (gradient h (φ t)) (y - x)) t := h_deriv t
    have h2 : HasDerivAt (fun _ : Real => h x) 0 t := hasDerivAt_const t (h x)
    have h3 : HasDerivAt (fun s : Real => s * inner Real (gradient h x) (y - x))
        (inner Real (gradient h x) (y - x)) t := by
      simpa using
        (hasDerivAt_id t |>.mul_const (inner Real (gradient h x) (y - x)))
    have h4 : HasDerivAt (fun s : Real => (L / 2) * s ^ 2 * ‖y - x‖ ^ 2)
        (L * t * ‖y - x‖ ^ 2) t := by
      have hs : HasDerivAt (fun s : Real => s ^ 2) (2 * t) t := by
        simpa [Nat.cast_ofNat] using hasDerivAt_pow 2 t
      convert (hs.const_mul (L / 2)).mul_const (‖y - x‖ ^ 2) using 1
      ring
    have hderiv := ((h1.sub h2).sub h3).sub h4
    simpa [q, sub_sub, inner_sub_left] using hderiv
  have hq_diff (t : Real) : DifferentiableAt Real q t :=
    (hq_deriv t).differentiableAt
  have hq_cont : Continuous q :=
    continuous_iff_continuousAt.mpr fun t => (hq_diff t).continuousAt
  have hq_contOn : ContinuousOn q (Set.Icc (0 : Real) 1) := hq_cont.continuousOn
  have hq_diffOn : DifferentiableOn Real q (Set.Ioo (0 : Real) 1) :=
    fun t _ => (hq_diff t).differentiableWithinAt
  have h_deriv_nonpos {t : Real} (ht : 0 < t) :
      inner Real (gradient h (φ t) - gradient h x) (y - x) -
          L * t * ‖y - x‖ ^ 2 <= 0 := by
    have h_cauchy :
        inner Real (gradient h (φ t) - gradient h x) (y - x) <=
          ‖gradient h (φ t) - gradient h x‖ * ‖y - x‖ :=
      real_inner_le_norm _ _
    have h_lip : ‖gradient h (φ t) - gradient h x‖ <= L * ‖φ t - x‖ :=
      hL.2.2 (φ t) x
    have h_norm_φ : ‖φ t - x‖ = t * ‖y - x‖ := by
      have hdist : dist x (AffineMap.lineMap x y t) = ‖t‖ * dist x y :=
        dist_left_lineMap x y t
      have htnorm : ‖t‖ = t := abs_of_pos ht
      simpa [φ, dist_eq_norm, norm_sub_rev, htnorm, mul_comm] using hdist
    have h_inner_bound :
        inner Real (gradient h (φ t) - gradient h x) (y - x) <=
          L * t * ‖y - x‖ ^ 2 := by
      calc
        inner Real (gradient h (φ t) - gradient h x) (y - x)
            <= ‖gradient h (φ t) - gradient h x‖ * ‖y - x‖ := h_cauchy
        _ <= (L * ‖φ t - x‖) * ‖y - x‖ := by
          nlinarith [h_lip, norm_nonneg (y - x)]
        _ = L * t * ‖y - x‖ ^ 2 := by
          rw [h_norm_φ]
          ring
    linarith
  have h_mvt : ∃ c ∈ Set.Ioo (0 : Real) 1, deriv q c = (q 1 - q 0) / (1 - 0) :=
    exists_deriv_eq_slope q (by norm_num : (0 : Real) < 1) hq_contOn hq_diffOn
  rcases h_mvt with ⟨c, hc, hc_eq⟩
  have h_deriv_c :
      deriv q c =
        inner Real (gradient h (φ c) - gradient h x) (y - x) -
          L * c * ‖y - x‖ ^ 2 :=
    (hq_deriv c).deriv
  have h_deriv_c_nonpos : deriv q c <= 0 := by
    rw [h_deriv_c]
    exact h_deriv_nonpos hc.1
  rw [show (1 : Real) - 0 = 1 by norm_num, div_one, hq0, sub_zero] at hc_eq
  have hq1_nonpos : q 1 <= 0 := by linarith
  simp [q, φ] at hq1_nonpos
  linarith

end BotCsetnek2015
