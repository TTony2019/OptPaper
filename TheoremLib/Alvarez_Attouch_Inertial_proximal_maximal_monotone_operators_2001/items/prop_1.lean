import Foundation.Hilbert.WeakConvergence
import Foundation.SetValued.Monotone
import TheoremLib.Attouch_Inertial_Proximal_Method_2000.items.lem_2
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.thm_1
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.ext_def_1
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.ext_thm_1

namespace AlvarezAttouch2001

open Filter Topology SetValuedOperator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- For nondecreasing inertial parameters bounded by a number below `1 / 3`,
the increments are square summable and the inertial proximal iterates converge weakly. -/
theorem inertial_proximal_point_converges_of_monotone_parameters
    {A : SetValuedOperator H H} (hA : A.IsMaximalMonotone)
    (x : ℕ → H) (alpha lambda : ℕ → ℝ)
    (hiteration : InertialProximalPointAlgorithm A x alpha lambda)
    (hzeros : A.zeros.Nonempty)
    (hlambda : ∃ lambda0 : ℝ, 0 < lambda0 ∧ ∀ k : ℕ, lambda0 ≤ lambda k)
    (halpha : ∃ alpha0 : ℝ, 0 ≤ alpha0 ∧ alpha0 < 1 / 3 ∧
      (∀ k : ℕ, 0 ≤ alpha k ∧ alpha k ≤ alpha0) ∧ Monotone alpha) :
    Summable (fun k : ℕ => ‖x (k + 1) - x k‖ ^ 2) ∧
      ∃ xhat : H, xhat ∈ A.zeros ∧
        Tendsto (fun k => toWeakSpace ℝ H (x k)) atTop (𝓝 (toWeakSpace ℝ H xhat)) := by
  have halg : InertialProximalAlgorithm A x alpha lambda := by
    intro k hk
    exact hiteration.update k hk
  exact sufficient_condition_for_convergence hA x alpha lambda halg hzeros hlambda halpha

end AlvarezAttouch2001
