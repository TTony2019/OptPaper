import Mathlib
import Foundation.FixedPoint.Nonexpansive

namespace AbbasDynamical2015

open scoped Gradient

/-- Lemma 2.5: a Lipschitz gradient of a differentiable convex function is cocoercive. -/
theorem gradient_cocoercive_of_lipschitz {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Psi : H → ℝ) (tau : ℝ) (htau : 0 < tau)
    (hconvex : ConvexOn ℝ Set.univ Psi)
    (hgrad : ∀ x, HasGradientAt Psi (∇ Psi x) x)
    (hLipschitz : LipschitzWith ⟨tau, le_of_lt htau⟩ (∇ Psi)) :
    CocoerciveOn tau⁻¹ Set.univ (fun x : Set.univ ↦ ∇ Psi x) := by
  have hdiff : Differentiable ℝ Psi := fun x => (hgrad x).differentiableAt
  have hLipschitz' : LipschitzWith (Real.toNNReal tau) (∇ Psi) := by
    simpa [Real.toNNReal_of_nonneg htau.le] using hLipschitz
  simpa [one_div] using baillon_haddad Psi (∇ Psi) tau htau hconvex hdiff hgrad hLipschitz'

end AbbasDynamical2015
