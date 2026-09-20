import Mathlib
import Foundation.Hilbert.Basic
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.ext_def_1
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.ext_def_2
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.ext_def_7

namespace BotCsetnek2015

lemma descent_of_hasLipschitzContinuousGradient {m : ℕ}
    (u : EuclideanSpace m → ℝ) (L : ℝ)
    (hL : HasLipschitzContinuousGradient u L) :
    ∀ x y : EuclideanSpace m,
      u y ≤ u x + inner ℝ (gradient u x) (y - x) + (L / 2) * ‖y - x‖ ^ 2 := by
  intro x y
  let φ : ℝ → EuclideanSpace m := fun t ↦ AffineMap.lineMap x y t
  let q : ℝ → ℝ := fun t ↦
    u (φ t) - u x - t * inner ℝ (gradient u x) (y - x) -
      (L / 2) * t ^ 2 * ‖y - x‖ ^ 2
  have hq0 : q 0 = 0 := by
    simp [q, φ]
  have h_deriv (t₀ : ℝ) :
      HasDerivAt (fun t : ℝ ↦ u (φ t))
        (inner ℝ (gradient u (φ t₀)) (y - x)) t₀ := by
    have hu_diffAt : DifferentiableAt ℝ u (φ t₀) := hL.2.1.differentiableAt
    have hline : HasDerivAt φ (y - x) t₀ := by
      simpa [φ] using
        (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t₀))
    have hcomp :
        HasDerivAt (fun t : ℝ ↦ u (φ t)) ((fderiv ℝ u (φ t₀)) (y - x)) t₀ :=
      hu_diffAt.hasFDerivAt.comp_hasDerivAt t₀ hline
    have hgrad :
        (fderiv ℝ u (φ t₀)) (y - x) =
          inner ℝ (gradient u (φ t₀)) (y - x) := by
      exact (inner_gradient_left hu_diffAt).symm
    simpa [hgrad]
      using hcomp
  have hq_deriv (t : ℝ) :
      HasDerivAt q
        (inner ℝ (gradient u (φ t) - gradient u x) (y - x) -
          L * t * ‖y - x‖ ^ 2) t := by
    have h1 : HasDerivAt (fun s : ℝ ↦ u (φ s))
        (inner ℝ (gradient u (φ t)) (y - x)) t := h_deriv t
    have h2 : HasDerivAt (fun _ : ℝ ↦ u x) 0 t := hasDerivAt_const t (u x)
    have h3 : HasDerivAt (fun s : ℝ ↦ s * inner ℝ (gradient u x) (y - x))
        (inner ℝ (gradient u x) (y - x)) t :=
      by simpa using
        (hasDerivAt_id t |>.mul_const (inner ℝ (gradient u x) (y - x)))
    have h4 : HasDerivAt (fun s : ℝ ↦ (L / 2) * s ^ 2 * ‖y - x‖ ^ 2)
        (L * t * ‖y - x‖ ^ 2) t := by
      have hs : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * t) t := by
        simpa [Nat.cast_ofNat] using hasDerivAt_pow 2 t
      convert (hs.const_mul (L / 2)).mul_const (‖y - x‖ ^ 2) using 1
      ring
    have h :=
      ((h1.sub h2).sub h3).sub h4
    simpa [q, sub_sub, inner_sub_left] using h
  have hq_diff (t : ℝ) : DifferentiableAt ℝ q t :=
    (hq_deriv t).differentiableAt
  have hq_cont : Continuous q :=
    continuous_iff_continuousAt.mpr fun t ↦ (hq_diff t).continuousAt
  have hq_contOn : ContinuousOn q (Set.Icc (0 : ℝ) 1) := hq_cont.continuousOn
  have hq_diffOn : DifferentiableOn ℝ q (Set.Ioo (0 : ℝ) 1) :=
    fun t _ ↦ (hq_diff t).differentiableWithinAt
  have h_deriv_nonpos {t : ℝ} (ht : 0 < t) :
      inner ℝ (gradient u (φ t) - gradient u x) (y - x) -
          L * t * ‖y - x‖ ^ 2 ≤ 0 := by
    have h_cauchy :
        inner ℝ (gradient u (φ t) - gradient u x) (y - x) ≤
          ‖gradient u (φ t) - gradient u x‖ * ‖y - x‖ :=
      real_inner_le_norm _ _
    have h_lip : ‖gradient u (φ t) - gradient u x‖ ≤ L * ‖φ t - x‖ :=
      hL.2.2 (φ t) x
    have h_norm_φ : ‖φ t - x‖ = t * ‖y - x‖ := by
      have hdist : dist x (AffineMap.lineMap x y t) = ‖t‖ * dist x y :=
        dist_left_lineMap x y t
      have htnorm : ‖t‖ = t := abs_of_pos ht
      simpa [φ, dist_eq_norm, norm_sub_rev, htnorm, mul_comm] using hdist
    have h_inner_bound :
        inner ℝ (gradient u (φ t) - gradient u x) (y - x) ≤
          L * t * ‖y - x‖ ^ 2 := by
      calc
        inner ℝ (gradient u (φ t) - gradient u x) (y - x)
            ≤ ‖gradient u (φ t) - gradient u x‖ * ‖y - x‖ := h_cauchy
        _ ≤ (L * ‖φ t - x‖) * ‖y - x‖ := by
          nlinarith [h_lip, norm_nonneg (y - x)]
        _ = L * t * ‖y - x‖ ^ 2 := by
          rw [h_norm_φ]
          ring
    linarith
  have h_mvt : ∃ c ∈ Set.Ioo (0 : ℝ) 1, deriv q c = (q 1 - q 0) / (1 - 0) :=
    exists_deriv_eq_slope q (by norm_num : (0 : ℝ) < 1) hq_contOn hq_diffOn
  rcases h_mvt with ⟨c, hc, hc_eq⟩
  have h_deriv_c :
      deriv q c =
        inner ℝ (gradient u (φ c) - gradient u x) (y - x) -
          L * c * ‖y - x‖ ^ 2 :=
    (hq_deriv c).deriv
  have h_deriv_c_nonpos : deriv q c ≤ 0 := by
    rw [h_deriv_c]
    exact h_deriv_nonpos hc.1
  rw [show (1 : ℝ) - 0 = 1 by norm_num, div_one, hq0, sub_zero] at hc_eq
  have hq1_nonpos : q 1 ≤ 0 := by linarith
  simp [q, φ] at hq1_nonpos
  linarith

/-- Bregman distance quadratic lower and upper bounds. -/
theorem bregmanDistance_quadratic_bounds {m : ℕ} (u : EuclideanSpace m → ℝ)
    (sigma Lgrad_u : ℝ)
    (hstrong : StronglyConvexWith sigma u)
    (hgrad : HasLipschitzContinuousGradient u Lgrad_u) :
    ∀ x y : EuclideanSpace m,
      (sigma / 2) * ‖x - y‖ ^ 2 ≤ bregmanDistance u x y ∧
        bregmanDistance u x y ≤ (Lgrad_u / 2) * ‖x - y‖ ^ 2 := by
  intro x y
  constructor
  · let G : EuclideanSpace m → ℝ :=
      fun z ↦ u z - (sigma / 2) * ‖z‖ ^ 2
    let φ : ℝ → ℝ := fun t ↦ G (AffineMap.lineMap y x t)
    have hφ_conv : ConvexOn ℝ Set.univ φ := by
      simpa [G, φ] using
        (hstrong.2.comp_affineMap (AffineMap.lineMap y x : ℝ →ᵃ[ℝ] EuclideanSpace m))
    have hu_diff : Differentiable ℝ u := hgrad.2.1
    have hu_line :
        HasDerivAt (fun t : ℝ ↦ u (AffineMap.lineMap y x t))
          (inner ℝ (gradient u y) (x - y)) 0 := by
      have huy : HasFDerivAt u (fderiv ℝ u y) y := (hu_diff y).hasFDerivAt
      have hline : HasDerivAt (AffineMap.lineMap y x : ℝ → EuclideanSpace m) (x - y) 0 :=
        AffineMap.hasDerivAt_lineMap
      have hcomp :=
        HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) huy hline (by simp)
      have hfderiv_apply :
          fderiv ℝ u y (x - y) = inner ℝ (gradient u y) (x - y) := by
        exact (inner_gradient_left (𝕜 := ℝ) (f := u) (x := y) (y := x - y)
          (hu_diff y)).symm
      simpa [Function.comp_def, hfderiv_apply] using hcomp
    have hnorm_line :
        HasDerivAt (fun t : ℝ ↦ ‖AffineMap.lineMap y x t‖ ^ 2)
          (2 * inner ℝ y (x - y)) 0 := by
      simpa using
        (AffineMap.hasDerivAt_lineMap (a := y) (b := x) (x := (0 : ℝ))).norm_sq
    have hφ_deriv :
        HasDerivAt φ
          (inner ℝ (gradient u y) (x - y) -
            (sigma / 2) * (2 * inner ℝ y (x - y))) 0 := by
      unfold φ G
      exact hu_line.sub (hnorm_line.const_mul (sigma / 2))
    have hderiv_eq :
        deriv φ 0 =
          inner ℝ (gradient u y) (x - y) -
            (sigma / 2) * (2 * inner ℝ y (x - y)) :=
      hφ_deriv.deriv
    have hφ_diff : DifferentiableAt ℝ φ 0 := hφ_deriv.differentiableAt
    have hslope := hφ_conv.deriv_le_slope (x := (0 : ℝ)) (y := (1 : ℝ))
      (by simp) (by simp) (by norm_num) hφ_diff
    rw [hderiv_eq] at hslope
    dsimp [slope, φ, G, bregmanDistance] at hslope ⊢
    rw [show AffineMap.lineMap y x (0 : ℝ) = y by simp,
      show AffineMap.lineMap y x (1 : ℝ) = x by simp] at hslope
    norm_num at hslope
    have hnorm_id : ‖x‖ ^ 2 = ‖y‖ ^ 2 + 2 * inner ℝ y (x - y) + ‖x - y‖ ^ 2 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (norm_add_sq_real y (x - y))
    nlinarith [hnorm_id, hstrong.1]
  · have hdescent :=
      descent_of_hasLipschitzContinuousGradient u Lgrad_u hgrad y x
    dsimp [bregmanDistance] at hdescent ⊢
    linarith

end BotCsetnek2015
