import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_2015.items.thm_1
import Mathlib

namespace AbbasDynamical2015

open MeasureTheory

/-- Remark 2.3: Theorem 2.1 persists for a positive locally absolutely continuous parameter. -/
def remark_2_3_variable_regularization {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (_hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (lam : ℝ → ℝ) (beta : ℝ) (x0 v0 : H)
    (_hlam_pos : ∀ t, 0 ≤ t → 0 < lam t)
    (_hlam_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval lam 0 b)
    (_hbeta : 0 < beta) (_hB : CocoerciveOn beta Set.univ (fun x : Set.univ ↦ B x))
    (_hv0 : v0 ∈ ERealFunction.subdifferential Phi x0) : Prop :=
    ∃! xv : (ℝ → H) × (ℝ → H),
      (∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval xv.1 0 b) ∧
      (∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval xv.2 0 b) ∧
      (∀ t, 0 ≤ t → xv.2 t ∈ ERealFunction.subdifferential Phi (xv.1 t)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ici 0),
        lam t • deriv xv.1 t + deriv xv.2 t + xv.2 t + B (xv.1 t) = 0) ∧
      xv.1 0 = x0 ∧ xv.2 0 = v0

end AbbasDynamical2015
