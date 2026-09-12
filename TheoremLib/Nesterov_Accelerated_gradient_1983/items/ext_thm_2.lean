import Mathlib

open scoped InnerProductSpace

namespace Nesterov1983

/-- The first-order inequality for a differentiable convex function. -/
theorem convex_firstOrder_inequality {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (hconv : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ u, HasGradientAt f (gradient f u) u) (u v : E) :
    f u + inner ℝ (gradient f u) (v - u) ≤ f v := by
  let φ : ℝ → ℝ := f ∘ AffineMap.lineMap u v
  have hφconvex : ConvexOn ℝ Set.univ φ := by
    simpa [φ] using hconv.comp_affineMap (AffineMap.lineMap u v)
  have hpath : HasDerivAt (fun t : ℝ ↦ u + t • (v - u)) (v - u) 0 := by
    convert (hasDerivAt_const (𝕜 := ℝ) 0 u).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const (v - u)) using 1
    all_goals simp
  have houter : HasFDerivAt f (InnerProductSpace.toDual ℝ E (gradient f u))
      ((fun t : ℝ ↦ u + t • (v - u)) 0) := by
    simpa using (hgrad u).hasFDerivAt
  have hφderiv : HasDerivAt φ (inner ℝ (gradient f u) (v - u)) 0 := by
    simpa [φ, Function.comp_def, AffineMap.lineMap_apply, add_comm, one_smul,
      add_zero, InnerProductSpace.toDual_apply_apply] using
      houter.comp_hasDerivAt 0 hpath
  have hslope := hφconvex.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one hφderiv
  have hdir : inner ℝ (gradient f u) (v - u) ≤ f v - f u := by
    simpa [φ, slope, Function.comp_def, AffineMap.lineMap_apply, zero_smul,
      one_smul, zero_add, add_zero] using hslope
  linarith

end Nesterov1983
