import Mathlib
import Foundation.Differentiation.ODE

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

/-- Global autonomous Cauchy--Lipschitz existence.  Supplied canonically by
  Foundation as `exists_global_solution_of_lipschitz` (isolated from the
  regularity translation used in `ext_thm_5`). -/
recall exists_global_solution_of_lipschitz

/-- The unique global classical (`C¹`) solution theorem.  Supplied canonically
  by Foundation as `exists_unique_global_solution_of_lipschitz`. -/
recall exists_unique_global_solution_of_lipschitz

/-- The classical Cauchy--Lipschitz--Picard statement referred to after
  Definition 2.3 (and in the proof of Corollary 4.3): an autonomous ordinary
  differential equation `ẋ = F(x)` on a Banach space with `L`-Lipschitz `F`
  has a unique global classical (`C¹`) solution for each initial value.
  Supplied canonically by Foundation.

  Deviations: the paper has no numbered result here; it applies CLP to the
  first-order system in the product space `H × H` and concludes that the
  solution is `C²((0,+∞);H)`, whereas this statement is the abstract
  `C¹`-solution form on a single Banach space `X`. -/
abbrev ext_thm_5 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (F : X → X) (L : ℝ) (hL : 0 < L) (hlip : ∀ x y : X, ‖F x - F y‖ ≤ L * ‖x - y‖)
    (x₀ : X) :
    ∃! x : ℝ → X, (Differentiable ℝ x ∧ Continuous (deriv x) ∧
      ∀ t : ℝ, deriv x t = F (x t) ∧ x 0 = x₀) :=
  exists_unique_global_solution_of_lipschitz F L hL hlip x₀

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
