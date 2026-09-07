import Mathlib
import Foundation.Optimization.Argmin
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.thm_3
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_1
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_2

namespace Alvarez2002
open Filter

/--
Proposition 5.2: (Human checked)
Even convex potentials give strong convergence of `(DIN)` trajectories.
-/
theorem din_strong_convergence_of_even_potential {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H] (Φ : H → ℝ) (α β : ℝ) (x : ℝ → H)
  (hΦ : AssumptionH H Φ) (hconvex : ConvexOn ℝ Set.univ Φ)
  (hmin : (Optimization.argminSet Φ).Nonempty)
  (hsol : IsDINTrajectory H Φ α β x)
  (hx : ContDiff ℝ 2 x)
  (hαβ : α * β ≤ 1)
  (heven : ∀ y, Φ y = Φ (-y)) :
  ∃ z, z ∈ Optimization.argminSet Φ ∧ Tendsto x atTop (nhds z) := by
  have hweak := din_weakly_converges_to_argmin Φ α β x hΦ hconvex hmin hsol
  rcases hweak with ⟨hdist, ⟨z, hzmin, hzweak⟩⟩
  have hzarg : z ∈ Optimization.argminSet Φ := by
    exact hzmin
  have hzero : (0 : H) ∈ Optimization.argminSet Φ := by
    intro y
    have hmid : Φ ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • (-y)) ≤
        (1 / 2 : ℝ) • Φ y + (1 / 2 : ℝ) • Φ (-y) := by
      exact hconvex.2 (show y ∈ Set.univ by trivial) (show -y ∈ Set.univ by trivial)
        (by norm_num) (by norm_num) (by norm_num)
    have hzero_eq : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • (-y) = (0 : H) := by
      module
    rw [hzero_eq] at hmid
    have heven' : Φ (-y) = Φ y := by simpa using (heven y).symm
    rw [heven'] at hmid
    have hmid' : Φ 0 ≤ (1 / 2 : ℝ) * Φ y + (1 / 2 : ℝ) * Φ y := by
      simpa [smul_eq_mul] using hmid
    nlinarith
  sorry
end Alvarez2002
