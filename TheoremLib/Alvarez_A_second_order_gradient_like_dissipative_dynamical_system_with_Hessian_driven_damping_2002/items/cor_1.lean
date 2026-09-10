import Mathlib
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_1
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_2
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.thm_1
namespace Alvarez2002
open Filter
/-- Coercivity bounds every `(DIN)` trajectory, hence yields Theorem 2.1(iii). -/
theorem coercive_potential_bounds_din {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (Φ : H → ℝ) (gradΦ : H → H) (hessΦ : H → H →L[ℝ] H) (α β : ℝ)
    (x v acc : ℝ → H) (hΦ : AssumptionH H Φ)
    (hhessΦ : ∀ R : ℝ, 0 < R → ∃ L : ℝ, 0 < L ∧ ∀ p q,
      ‖p‖ ≤ R → ‖q‖ ≤ R → ‖hessΦ p - hessΦ q‖ ≤ L * ‖p - q‖)
    (hgrad : ∀ x u, HasDerivAt (fun s : ℝ => Φ (x + s • u))
      (inner ℝ (gradΦ x) u) 0)
    (hcoercive : ∀ r : ℝ, ∃ R : ℝ, ∀ z, R ≤ ‖z‖ → r ≤ Φ z)
    (hsol : IsDINTrajectory H Φ α β x)
    (henergy : ∀ t,
      (α * β + 1) * Φ (x t) + (1 / 2) * ‖v t + β • gradΦ (x t)‖ ^ 2 ≤
        (α * β + 1) * Φ (x 0) + (1 / 2) * ‖v 0 + β • gradΦ (x 0)‖ ^ 2) :
    (∃ R : ℝ, ∀ t, ‖x t‖ ≤ R) ∧
      Bornology.IsBounded (Set.range v) ∧ Bornology.IsBounded (Set.range acc) ∧
      Bornology.IsBounded (Set.range (fun t => gradΦ (x t))) ∧
      Bornology.IsBounded (Set.range (fun t => hessΦ (x t))) ∧
      Tendsto v atTop (nhds 0) ∧ Tendsto acc atTop (nhds 0) ∧
      Tendsto (fun t => gradΦ (x t)) atTop (nhds 0) := by
  sorry

end Alvarez2002
