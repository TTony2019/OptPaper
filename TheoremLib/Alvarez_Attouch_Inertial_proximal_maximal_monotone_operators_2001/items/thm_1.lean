import Foundation.Hilbert.WeakConvergence
import Foundation.SetValued.Monotone
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.def_1
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.def_2
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.lem_1
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.ext_def_1
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.ext_thm_1
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.algo_1
import TheoremLib.Attouch_Inertial_Proximal_Method_2000.items.thm_1

namespace AlvarezAttouch2001

open Filter Topology SetValuedOperator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The inertial proximal point iterates converge weakly under the summability condition. -/
theorem inertial_proximal_point_converges
    {A : SetValuedOperator H H} (hA : A.IsMaximalMonotone)
    (x : ℕ → H) (alpha lambda : ℕ → ℝ)
    (hiteration : InertialProximalPointAlgorithm A x alpha lambda)
    (hzeros : A.zeros.Nonempty)
    (hlambda : ∃ lambda0 : ℝ, 0 < lambda0 ∧ ∀ k : ℕ, lambda0 ≤ lambda k)
    (halpha : ∃ alpha0 : ℝ, 0 ≤ alpha0 ∧ alpha0 < 1 ∧
      ∀ k : ℕ, 0 ≤ alpha k ∧ alpha k ≤ alpha0)
    (hsummable : Summable (fun k : ℕ => alpha (k + 1) * ‖x (k + 1) - x k‖ ^ 2)) :
    ∃ xhat : H, xhat ∈ A.zeros ∧
      Tendsto (fun k => toWeakSpace ℝ H (x k)) atTop (𝓝 (toWeakSpace ℝ H xhat)) := by
  have halg : InertialProximalAlgorithm A x alpha lambda := by
    intro k hk
    exact hiteration.update k hk
  exact convergence_of_inertial_proximal_method hA x alpha lambda halg hzeros hlambda halpha
    hsummable

end AlvarezAttouch2001
