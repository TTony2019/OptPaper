import Mathlib
import Foundation.Differentiation.Gateaux

namespace LorenzPock

private theorem convex_supporting_baillon_haddad {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f : H → ℝ) (grad : H → H)
    (hconvex : ConvexOn ℝ Set.univ f) (hgrad : ∀ z, HasGradientAt f (grad z) z)
    (z u : H) :
    f z + inner ℝ (grad z) (u - z) ≤ f u := by
  let φ : ℝ → ℝ := f ∘ AffineMap.lineMap z u
  have hφconvex : ConvexOn ℝ Set.univ φ := by
    simpa [φ] using hconvex.comp_affineMap (AffineMap.lineMap z u)
  have hpath : HasDerivAt (fun t : ℝ ↦ z + t • (u - z)) (u - z) 0 := by
    convert (hasDerivAt_const (𝕜 := ℝ) 0 z).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const (u - z)) using 1 <;> simp
  have houter : HasFDerivAt f (InnerProductSpace.toDual ℝ H (grad z))
      ((fun t : ℝ ↦ z + t • (u - z)) 0) := by
    simpa using (hgrad z).hasFDerivAt
  have hφderiv : HasDerivAt φ (inner ℝ (grad z) (u - z)) 0 := by
    simpa [φ, Function.comp_def, AffineMap.lineMap_apply, add_comm, one_smul, add_zero,
      InnerProductSpace.toDual_apply_apply] using
      HasFDerivAt.comp_hasDerivAt 0 houter hpath
  have hslope := hφconvex.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one hφderiv
  have : inner ℝ (grad z) (u - z) ≤ f u - f z := by
    simpa [φ, slope, Function.comp_def, AffineMap.lineMap_apply, zero_smul, one_smul,
      zero_add, add_zero] using hslope
  linarith

/-- Baillon--Haddad: the gradient of a convex function with `L`-Lipschitz
gradient is `1/L`-cocoercive. -/
theorem baillon_haddad {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (grad : H → H) (fderiv : H → H →L[ℝ] ℝ) (L : ℝ) (hL : 0 < L)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x, HasFDerivAt f (fderiv x) x)
    (hgradient : ∀ x v, fderiv x v = inner ℝ (grad x) v)
    (hgrad_lipschitz : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖) :
    (∀ x y, inner ℝ (grad x - grad y) (x - y) ≥ L⁻¹ * ‖grad x - grad y‖ ^ 2) := by
  have hHasGradient : ∀ z : H, HasGradientAt f (grad z) z := by
    intro z
    have hmap : fderiv z = InnerProductSpace.toDual ℝ H (grad z) := by
      ext v
      simpa [InnerProductSpace.toDual_apply_apply] using hgradient z v
    simpa [hmap] using hgrad z
  have hdiff : DifferentiableOn ℝ f Set.univ := fun z _ ↦ (hgrad z).differentiableAt.differentiableWithinAt
  have hgradientWithin : ∀ z : H, gradientWithin f Set.univ z = grad z := by
    intro z
    apply ext_inner_left ℝ
    intro v
    rw [← fderivWithin_eq_inner_gradientWithin (hdiff z (by simp)) uniqueDiffWithinAt_univ]
    rw [fderivWithin_univ, (hgrad z).fderiv]
    simpa [real_inner_comm] using hgradient z v
  let β : NNReal := ⟨L, hL.le⟩
  have hlip : LipschitzOnWith β (gradientWithin f Set.univ) Set.univ := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x _ y _
    rw [dist_eq_norm, dist_eq_norm, hgradientWithin x, hgradientWithin y]
    simpa [β] using hgrad_lipschitz x y
  have hsmooth : ∀ z u : H,
      f u ≤ f z + inner ℝ (grad z) (u - z) + (L / 2) * ‖u - z‖ ^ 2 := by
    intro z u
    have habs := abs_sub_sub_inner_gradientWithin_le_half_mul (U := Set.univ) (β := β)
      isOpen_univ convex_univ hdiff hlip (x := z) (y := u) (by simp) (by simp)
    have hrem : f u - f z - inner ℝ (grad z) (u - z) ≤ (L / 2) * ‖u - z‖ ^ 2 := by
      calc
        f u - f z - inner ℝ (grad z) (u - z) ≤
            |f u - f z - inner ℝ (grad z) (u - z)| := le_abs_self _
        _ = |f u - f z - inner ℝ (u - z) (gradientWithin f Set.univ z)| := by
          rw [hgradientWithin z, real_inner_comm]
        _ ≤ ((β : ℝ) / 2) * ‖u - z‖ ^ 2 := habs
        _ = (L / 2) * ‖u - z‖ ^ 2 := by
          change (L / 2) * ‖u - z‖ ^ 2 = (L / 2) * ‖u - z‖ ^ 2
          rfl
    nlinarith
  have hBregman : ∀ x y : H,
      (2 * L)⁻¹ * ‖grad x - grad y‖ ^ 2 ≤
        f x - f y - inner ℝ (grad y) (x - y) := by
    intro x y
    let d : H := grad x - grad y
    let w : H := x - L⁻¹ • d
    have hlow := convex_supporting_baillon_haddad f grad hconvex hHasGradient y w
    have hupp := hsmooth x w
    have h := hlow.trans hupp
    have hwx : w - x = -L⁻¹ • d := by
      dsimp [w]
      module
    have hwy : w - y = x - y - L⁻¹ • d := by
      dsimp [w]
      module
    have hgd : inner ℝ (grad x) d - inner ℝ (grad y) d = ‖d‖ ^ 2 := by
      dsimp [d]
      rw [← inner_sub_left, real_inner_self_eq_norm_sq]
    have hkey : L⁻¹ * ‖d‖ ^ 2 - (L / 2) * ‖-(L⁻¹ • d)‖ ^ 2 ≤
        f x - f y - inner ℝ (grad y) (x - y) := by
      rw [hwy, hwx, inner_sub_right, real_inner_smul_right] at h
      rw [show -L⁻¹ • d = -(L⁻¹ • d) by module] at h
      rw [inner_neg_right, real_inner_smul_right] at h
      have hscaled := congrArg (fun t : ℝ ↦ L⁻¹ * t) hgd
      ring_nf at hscaled
      nlinarith [hscaled]
    have hinv : 0 < L⁻¹ := inv_pos.mpr hL
    have hnorm : ‖-(L⁻¹ • d)‖ ^ 2 = (L⁻¹) ^ 2 * ‖d‖ ^ 2 := by
      rw [norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_pos hinv]
      ring
    rw [hnorm] at hkey
    have hcoef : L⁻¹ * ‖d‖ ^ 2 - (L / 2) * (L⁻¹) ^ 2 * ‖d‖ ^ 2 =
        (2 * L)⁻¹ * ‖d‖ ^ 2 := by
      field_simp [hL.ne']
      ring
    have hkey' : L⁻¹ * ‖d‖ ^ 2 - (L / 2) * (L⁻¹) ^ 2 * ‖d‖ ^ 2 ≤
        f x - f y - inner ℝ (grad y) (x - y) := by
      nlinarith [hkey]
    rw [hcoef] at hkey'
    simpa [d] using hkey'
  intro x y
  have hxy := hBregman x y
  have hyx := hBregman y x
  have hsum := add_le_add hxy hyx
  have hnorm : ‖grad y - grad x‖ ^ 2 = ‖grad x - grad y‖ ^ 2 := by
    rw [show grad y - grad x = -(grad x - grad y) by abel, norm_neg]
  rw [hnorm] at hsum
  have hinner :
      (f x - f y - inner ℝ (grad y) (x - y)) +
        (f y - f x - inner ℝ (grad x) (y - x)) =
        inner ℝ (grad x - grad y) (x - y) := by
    rw [show y - x = -(x - y) by abel, inner_neg_right, inner_sub_left]
    ring
  rw [hinner] at hsum
  have hcoef :
      (2 * L)⁻¹ * ‖grad x - grad y‖ ^ 2 + (2 * L)⁻¹ * ‖grad x - grad y‖ ^ 2 =
        L⁻¹ * ‖grad x - grad y‖ ^ 2 := by
    field_simp [hL.ne']
    ring
  rw [hcoef] at hsum
  exact hsum

end LorenzPock
