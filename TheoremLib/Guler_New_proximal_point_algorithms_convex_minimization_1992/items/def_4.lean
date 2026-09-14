import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_3
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_4

open ERealFunction

/-- Criterion A': an approximate minimizer has small proximal subdifferential residual.

The paper writes this as `rho (0, subdiff phi_k (x_{k+1})) <= epsilon_k / lambda_k`.
The separate witness form below is recorded because the proof of Lemma 3.1 uses an
actual subgradient attaining this bound; in finite-dimensional Euclidean space the
subdifferential is closed and convex, so the two formulations agree whenever it is
nonempty. -/
def IsApproximationMinimizer {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (lam ε : ℝ) (y x : H) : Prop :=
  0 < lam ∧
    (subdifferential (fun z => (proximalObjective f lam y z : EReal)) x).Nonempty ∧
      subdifferentialResidual (proximalObjective f lam y) x ≤ ε / lam

/-- The attained form of criterion A' used by the quantitative error lemmas;
the positivity of `lam` is part of the paper's proximal-parameter condition. -/
def IsApproximationMinimizerWitness {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (lam ε : ℝ) (y x : H) : Prop :=
  0 < lam ∧
    ∃ w : H,
      w ∈ subdifferential (fun z => (proximalObjective f lam y z : EReal)) x ∧
        ‖w‖ ≤ ε / lam
