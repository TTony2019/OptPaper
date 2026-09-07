import Mathlib
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.thm_1

namespace AttouchPeypouquetRedont2014

/-- Remark 15 records that Theorem 1 applies through alternative (iv) when `Ψ` is convex. -/
theorem remark15 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (phi Θ : H → EReal) (Ψ : H → ℝ) (gradPsi : H → H) (a b lam Lpsi : ℝ) (u y : ℕ → H)
    (hH : IFBHypothesis phi Θ Ψ gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi Ψ gradPsi a b lam u y)
    (hconvex : Convex ℝ (ERealFunction.epigraph fun x ↦ (Ψ x : EReal)))
    (hS : (Optimization.argminSet Θ).Nonempty) :
    ∃ q ∈ Optimization.argminSet Θ, Filter.Tendsto (fun k ↦ toWeakSpace ℝ H (u k)) Filter.atTop
      (nhds (toWeakSpace ℝ H q)) :=
  (theorem1 phi Θ Ψ gradPsi a b lam Lpsi u y hH hIFB).2.1
    ⟨hS, Or.inr (Or.inr (Or.inr hconvex))⟩

end AttouchPeypouquetRedont2014
