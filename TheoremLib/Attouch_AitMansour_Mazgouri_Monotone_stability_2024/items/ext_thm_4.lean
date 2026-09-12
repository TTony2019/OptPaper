import Mathlib
import Foundation.FixedPoint.Nonexpansive
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_1
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_2

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

/-! Item `ext_thm_4`: the Baillon--Haddad theorem is supplied canonically by
  Foundation (`Foundation.FixedPoint.Nonexpansive`).  The paper's conclusion
  `IsCocoercive gradf (1/L)` is Foundation's
  `CocoerciveOn (1/L) Set.univ (fun x : Set.univ => gradf x)`; the hypothesis
  `IsConvex f` is converted to Foundation's `ConvexOn ℝ Set.univ f` by
  `isConvexOn_univ_of_IsConvex`, and the paper's `IsLipschitzContinuous gradf L`
  is mathlib's `LipschitzWith (Real.toNNReal L) gradf`. -/

/-- The gradient supporting hyperplane bound.  Supplied canonically by
  Foundation. -/
recall convex_supporting_baillon_haddad

/-- The quadratic upper bound of a function with Lipschitz gradient.  Supplied
  canonically by Foundation. -/
recall smoothness_baillon_haddad

/-- The Baillon--Haddad theorem, supplied canonically by Foundation. -/
recall baillon_haddad

/-- Bridge: the paper's `IsConvex` (real Jensen form) implies Foundation's
  `ConvexOn ℝ Set.univ`. -/
theorem isConvexOn_univ_of_IsConvex {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : H → ℝ} (hf : IsConvex f) : ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hb_eq : b = 1 - a := by linarith
  subst b
  simpa using hf x y a ha (by linarith)

/-- Baillon-Haddad Theorem: For a convex differentiable function f with
  L-Lipschitz gradient gradf = ∇f (via Riesz representation), its gradient
  is 1/L-cocoercive. The paper invokes this as [22, Corollary 18.16] with
  L=1/β.  Supplied canonically by Foundation. -/
abbrev ext_thm_4 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (gradf : H → H) (L : ℝ) (hL : 0 < L)
    (hconv : IsConvex f) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x, HasGradientAt f (gradf x) x)
    (hlip : LipschitzWith (Real.toNNReal L) gradf) :
    CocoerciveOn (1 / L) Set.univ (fun x : Set.univ => gradf x) :=
  baillon_haddad f gradf L hL (isConvexOn_univ_of_IsConvex hconv) hdiff hgrad hlip

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
