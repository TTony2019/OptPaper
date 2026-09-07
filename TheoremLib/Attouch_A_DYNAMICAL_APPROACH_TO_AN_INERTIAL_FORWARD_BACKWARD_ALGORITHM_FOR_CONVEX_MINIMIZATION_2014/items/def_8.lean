import Mathlib
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_3
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_7

namespace AttouchPeypouquetRedont2014

/-- Liapunov-type sequence `F_k(q)` of (3.12). -/
noncomputable def liapunovF {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u y : ℕ → H) (a b lam : ℝ) (q : H) (k : ℕ) (hk : 1 ≤ k) : ℝ :=
  let α := (1 + b * lam) / (2 * lam ^ 2)
  let δ := (2 + (b - a) * lam) / (2 * lam ^ 2)
  let hk' : 2 ≤ k + 1 := by omega
  let Gk : ℝ := auxiliaryG u y a b lam q (k + 1) hk'
  (a + b) / (2 * lam) * ‖u k - q‖ ^ 2 -
    (1 / lam + b) * Gk -
    δ * ∑ i ∈ (Finset.Icc 2 k).attach,
      ‖velocity u i (by
        have hi : 2 ≤ (i : ℕ) := (Finset.mem_Icc.mp i.property).1
        omega)‖ ^ 2 +
    2 * α * inner ℝ (velocity u (k + 1) (by omega)) (u k - q)

end AttouchPeypouquetRedont2014
